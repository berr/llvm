#define DEBUG_TYPE "regalloc"
#include "llvm/CodeGen/Passes.h"
#include "AllocationOrder.h"
#include "LiveDebugVariables.h"
#include "RegAllocBase.h"
#include "Spiller.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/CodeGen/CalcSpillWeights.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveRangeEdit.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/VirtRegMap.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include <cstdlib>
#include <vector>

using namespace llvm;

static RegisterRegAlloc basicRegAlloc("ai", "ai register allocator", createAIRegisterAllocator);

namespace {
  struct CompSpillWeight {
    bool operator()(LiveInterval *A, LiveInterval *B) const {
      // Order in reverser order, so we put the elements inside our regular Queue.
      return A->weight >= B->weight;
    }
  };
}

namespace {


class RAIA : public MachineFunctionPass, public RegAllocBase
{
  // context
  MachineFunction *MF;

  // state
  std::auto_ptr<Spiller> SpillerInstance;



  // Scratch space.  Allocated here to avoid repeated malloc calls in
  // selectOrSplit().
  BitVector UsableRegs;

public:
  RAIA();

  /// Return the pass name.
  virtual const char* getPassName() const {
    return "AI Register Allocator";
  }

  /// RAIA analysis usage.
  virtual void getAnalysisUsage(AnalysisUsage &AU) const;

  virtual void releaseMemory();

  virtual Spiller &spiller() { return *SpillerInstance; }

  virtual float getPriority(LiveInterval *LI) { return LI->weight; }

  virtual void enqueue(LiveInterval *LI) {
    // noop
  }

  virtual LiveInterval *dequeue() {
    // noop
    return 0;
  }

  void allocatePhysRegs();

  virtual unsigned selectOrSplit(LiveInterval &VirtReg,
                                 SmallVectorImpl<LiveInterval*> &SplitVRegs);

  /// Perform register allocation.
  virtual bool runOnMachineFunction(MachineFunction &mf);

  // Helper for spilling all live virtual registers currently unified under preg
  // that interfere with the most recently queried lvr.  Return true if spilling
  // was successful, and append any new spilled/split intervals to splitLVRs.
  bool spillInterferences(LiveInterval &VirtReg, unsigned PhysReg,
                          SmallVectorImpl<LiveInterval*> &SplitVRegs);

  static char ID;

private:

  bool allocateOrGetBestSpillable(LiveInterval& VirtReg, LiveInterval** Spillable, SmallVectorImpl<unsigned>& scratch_pad);
};

char RAIA::ID = 0;

} // end anonymous namespace

RAIA::RAIA(): MachineFunctionPass(ID) {
  initializeLiveDebugVariablesPass(*PassRegistry::getPassRegistry());
  initializeLiveIntervalsPass(*PassRegistry::getPassRegistry());
  initializeSlotIndexesPass(*PassRegistry::getPassRegistry());
  initializeRegisterCoalescerPass(*PassRegistry::getPassRegistry());
  initializeMachineSchedulerPass(*PassRegistry::getPassRegistry());
  initializeCalculateSpillWeightsPass(*PassRegistry::getPassRegistry());
  initializeLiveStacksPass(*PassRegistry::getPassRegistry());
  initializeMachineDominatorTreePass(*PassRegistry::getPassRegistry());
  initializeMachineLoopInfoPass(*PassRegistry::getPassRegistry());
  initializeVirtRegMapPass(*PassRegistry::getPassRegistry());
  initializeLiveRegMatrixPass(*PassRegistry::getPassRegistry());
}

void RAIA::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesCFG();
  AU.addRequired<AliasAnalysis>();
  AU.addPreserved<AliasAnalysis>();
  AU.addRequired<LiveIntervals>();
  AU.addPreserved<LiveIntervals>();
  AU.addPreserved<SlotIndexes>();
  AU.addRequired<LiveDebugVariables>();
  AU.addPreserved<LiveDebugVariables>();
  AU.addRequired<CalculateSpillWeights>();
  AU.addRequired<LiveStacks>();
  AU.addPreserved<LiveStacks>();
  AU.addRequiredID(MachineDominatorsID);
  AU.addPreservedID(MachineDominatorsID);
  AU.addRequired<MachineLoopInfo>();
  AU.addPreserved<MachineLoopInfo>();
  AU.addRequired<VirtRegMap>();
  AU.addPreserved<VirtRegMap>();
  AU.addRequired<LiveRegMatrix>();
  AU.addPreserved<LiveRegMatrix>();
  MachineFunctionPass::getAnalysisUsage(AU);
}

void RAIA::releaseMemory() {
  SpillerInstance.reset(0);
}


namespace {

struct RAIARegister{

  LiveInterval& Reg;
  int Value;

  RAIARegister(LiveInterval& Register) : Reg(Register), Value(0) { }

  virtual ~RAIARegister() { }

};

}

static bool RAIARegisterCompare(RAIARegister* first, RAIARegister* second){
  return first->Value < second->Value;
}

// Sort a sequence
static void sortSequence(std::vector<RAIARegister*>& values){
  std::sort(values.begin(), values.end(), RAIARegisterCompare);
}

// Generate a new sequence
static void randomizeOrder(std::vector<RAIARegister*>& values){

  for (std::vector<RAIARegister*>::iterator i = values.begin(),
      end = values.end(); i != end; ++i){
    RAIARegister* current  = *i;

    current->Value = std::rand();

  }

}

static void clearSequence(std::vector<RAIARegister*>& sequence) {
  while(sequence.size()) {
    RAIARegister* reg = sequence.back();
    sequence.pop_back();
    delete reg;
  }

}

namespace {

const int MAX_ITERATIONS = 5;
const int NUMBER_OF_BEES = 10;
const int NUMBER_OF_SOURCES = NUMBER_OF_BEES / 2;


}

bool RAIA::allocateOrGetBestSpillable(LiveInterval& VirtReg, LiveInterval** Spillable, SmallVectorImpl<unsigned>& PhysRegSpillCands){
  AllocationOrder Order(VirtReg.reg, *VRM, RegClassInfo);

  while (unsigned PhysReg = Order.next()) {
    // Check for interference in PhysReg
    switch (Matrix->checkInterference(VirtReg, PhysReg)) {
    case LiveRegMatrix::IK_Free:
      // PhysReg is available, allocate it.
      Matrix->assign(VirtReg, PhysReg);
      return true;

    case LiveRegMatrix::IK_VirtReg:
      // Only virtual registers in the way, we may be able to spill them.
      PhysRegSpillCands.push_back(PhysReg);
      break;

    default:
      // RegMask or RegUnit interference.
      // Do nothing becase we can try another physical register
      continue;
    }
  }


  LiveInterval* BestSpillCandidate = 0;

  // Find the live range with minimum spill weight
  for (SmallVectorImpl<unsigned>::iterator PhysRegI = PhysRegSpillCands.begin(),
         PhysRegE = PhysRegSpillCands.end(); PhysRegI != PhysRegE; ++PhysRegI) {

    unsigned PhysReg = *PhysRegI;

    for (MCRegUnitIterator Units(PhysReg, TRI); Units.isValid(); ++Units) {
      LiveIntervalUnion::Query &Q = Matrix->query(VirtReg, *Units);
      Q.collectInterferingVRegs();

      if (Q.seenUnspillableVReg()){
        continue;
      }

      for (unsigned i = Q.interferingVRegs().size(); i; --i) {
        LiveInterval *Intf = Q.interferingVRegs()[i - 1];

        if (!BestSpillCandidate || (Intf->isSpillable() && BestSpillCandidate->weight > Intf->weight))
          BestSpillCandidate = Intf;

      }
    }
  }

  // Did not find any better spillable register. Maybe we can still try this one
  if (VirtReg.isSpillable() && (!BestSpillCandidate || BestSpillCandidate->weight > VirtReg.weight)) {
    BestSpillCandidate = &VirtReg;
  }

  // Notify that this is the interfering LiveRange with minimum spill weight
  // May return 0 when there's no interfering LiveRange to split.
  *Spillable = BestSpillCandidate;
  return false;


}


void RAIA::allocatePhysRegs() {

  DEBUG(dbgs() << "Allocating using AI!" << "\n");

  std::vector<RAIARegister*> sources[NUMBER_OF_SOURCES];
  double fitness[NUMBER_OF_SOURCES];

  int iterations = 0;



  SmallVector<unsigned, 8> ScratchPad;
  SmallVector<LiveInterval*, 2> LiveRangeScratchPad;
  // Main allocation loop, stay here until we find a solution
  while (true) {

    Matrix->invalidateVirtRegs();

    // generate initial sequences
    for (unsigned i = 0, e = MRI->getNumVirtRegs(); i != e; ++i) {
      unsigned Reg = TargetRegisterInfo::index2VirtReg(i);

      // Register only used for debug instructions, we can ignore it
      if (MRI->reg_nodbg_empty(Reg)){
        DEBUG(dbgs() << "Doing nothing for register: " << Reg << "\n");
        continue;
      }

      LiveInterval& VirtReg = LIS->getInterval(Reg);

      for (int i = 0; i < NUMBER_OF_SOURCES; ++i){
        sources[i].push_back(new RAIARegister(VirtReg));
      }

    }

    Matrix->invalidateVirtRegs();


    for (int i = 0; i < NUMBER_OF_SOURCES; ++i){
      randomizeOrder(sources[i]);
      sortSequence(sources[i]);
    }


    iterations = 0;
    LiveInterval* BestGlobalSpillCandidate = 0;


    while (iterations < MAX_ITERATIONS) {
      DEBUG(dbgs() << "Allocating iteration: " << iterations << "\n");


      // Check if any of the sources meet the allocation criteria.
      for (int source_index = 0; source_index < NUMBER_OF_SOURCES; ++source_index){
        DEBUG(dbgs() << "Trying sequence number: " << source_index << "\n");

        std::vector<RAIARegister*> source = sources[source_index];
        int size = sources[source_index].size();
        int i;
        bool allocated = true;

        for(i = 0; i < size; ++i){
          RAIARegister* current = sources[source_index][i];
          LiveInterval* Spillable;


          if (MRI->reg_nodbg_empty(current->Reg.reg)) {
            LIS->removeInterval(current->Reg.reg);
            Matrix->invalidateVirtRegs();
            continue;
          }


          if (allocateOrGetBestSpillable(current->Reg, &Spillable, ScratchPad)){
            continue;
          }


          // We Could not allocate.

          // Do a generic update of the fitness of this Sequence
          fitness[source_index] = (float)(i) / size;


          // Dead end, we can not even split a live range.
          if (Spillable == 0){
            // Just notify, so we can generate another sequence
            fitness[source_index] = 0;
            DEBUG(dbgs() << "Unable to alloc for" << current->Reg << "\n");
          }

          // We found an interference.
          // Get the suggested spill LiveInterval and check if it has a lower cost than
          // the one we had before (if we had any).
          if (! BestGlobalSpillCandidate || BestGlobalSpillCandidate->weight > Spillable->weight){
            BestGlobalSpillCandidate = Spillable;
            DEBUG(dbgs() << "Updating BestCandidateToSpill: " << *BestGlobalSpillCandidate << "\n");
          }


          DEBUG(dbgs() << "Could not allocate! Undoing changes" << "\n");

          for (int j = 0; j < i; ++j){
            // Since we modified the LiveRangeMatrix, we have to undo all changes
            // The last element wasn't assigned
            RAIARegister* current = sources[source_index][j];

            LiveInterval& virtualReg = current->Reg;

            if (!MRI->reg_nodbg_empty(virtualReg.reg) && LIS->hasInterval(virtualReg.reg)){
              DEBUG(dbgs() << "Unassigning: " << current->Reg << "\n");
              Matrix->unassign(current->Reg);
            }

          }

          // We changed it a lot
          Matrix->invalidateVirtRegs();

          // We're done with this sequence.
          allocated = false;
          break;

        }


        // Found a possible allocation!
        if (allocated){
          DEBUG(dbgs() << "Successfull allocation!" << "\n");


          DEBUG(dbgs() << "Cleaning up sequences!" << "\n");
          for (int source_index = 0; source_index < NUMBER_OF_SOURCES; ++source_index){
              clearSequence(sources[source_index]);
          }

          return;
        }


      }


      for (int source_index = 0; source_index < NUMBER_OF_SOURCES; ++source_index){

        if (fitness[source_index] < 0.2) {
          DEBUG(dbgs() << "Source: " << source_index << " Dissatisfied\n");
          randomizeOrder(sources[source_index]);
        }
        else {
          // Find a neighboor solution
        }
      }

      ++iterations;
    }

    assert(BestGlobalSpillCandidate && "Allocation Failed because we can't spill");

    DEBUG(dbgs() << "Trying to spill: " << *BestGlobalSpillCandidate << "\n");
    LiveRangeScratchPad.clear();
    LiveRangeEdit LRE(BestGlobalSpillCandidate, LiveRangeScratchPad, *MF, *LIS, VRM);
    spiller().spill(LRE);

    DEBUG(dbgs() << "Cleaning up sequences!" << "\n");
    for (int source_index = 0; source_index < NUMBER_OF_SOURCES; ++source_index){
      clearSequence(sources[source_index]);
    }


  }

}



// Spill or split all live virtual registers currently unified under PhysReg
// that interfere with VirtReg. The newly spilled or split live intervals are
// returned by appending them to SplitVRegs.
bool RAIA::spillInterferences(LiveInterval &VirtReg, unsigned PhysReg,
                                 SmallVectorImpl<LiveInterval*> &SplitVRegs) {
  // Record each interference and determine if all are spillable before mutating
  // either the union or live intervals.
  SmallVector<LiveInterval*, 8> Intfs;

  // Collect interferences assigned to any alias of the physical register.
  for (MCRegUnitIterator Units(PhysReg, TRI); Units.isValid(); ++Units) {
    LiveIntervalUnion::Query &Q = Matrix->query(VirtReg, *Units);
    Q.collectInterferingVRegs();
    if (Q.seenUnspillableVReg())
      return false;
    for (unsigned i = Q.interferingVRegs().size(); i; --i) {
      LiveInterval *Intf = Q.interferingVRegs()[i - 1];
      if (!Intf->isSpillable() || Intf->weight > VirtReg.weight)
        return false;
      Intfs.push_back(Intf);
    }
  }
  DEBUG(dbgs() << "spilling " << TRI->getName(PhysReg) <<
        " interferences with " << VirtReg << "\n");
  assert(!Intfs.empty() && "expected interference");

  // Spill each interfering vreg allocated to PhysReg or an alias.
  for (unsigned i = 0, e = Intfs.size(); i != e; ++i) {
    LiveInterval &Spill = *Intfs[i];

    // Skip duplicates.
    if (!VRM->hasPhys(Spill.reg))
      continue;

    // Deallocate the interfering vreg by removing it from the union.
    // A LiveInterval instance may not be in a union during modification!
    Matrix->unassign(Spill);

    // Spill the extracted interval.
    LiveRangeEdit LRE(&Spill, SplitVRegs, *MF, *LIS, VRM);
    spiller().spill(LRE);
  }
  return true;
}


unsigned RAIA::selectOrSplit(LiveInterval &VirtReg, SmallVectorImpl<LiveInterval*> &SplitVRegs) {
  // Noop
  return 0;
}


////////////////////////////////////////////////////////////////////////////////
// Interface
////////////////////////////////////////////////////////////////////////////////

bool RAIA::runOnMachineFunction(MachineFunction &mf) {
  DEBUG(dbgs() << "********** AI REGISTER ALLOCATION **********\n"
               << "********** Function: "
               << mf.getName() << '\n');

  MF = &mf;
  RegAllocBase::init(getAnalysis<VirtRegMap>(),
                     getAnalysis<LiveIntervals>(),
                     getAnalysis<LiveRegMatrix>());
  SpillerInstance.reset(createInlineSpiller(*this, *MF, *VRM));

  allocatePhysRegs();

  // Diagnostic output before rewriting
  DEBUG(dbgs() << "Post alloc VirtRegMap:\n" << *VRM << "\n");

  releaseMemory();
  return true;
}

FunctionPass* llvm::createAIRegisterAllocator()
{
  return new RAIA();
}
