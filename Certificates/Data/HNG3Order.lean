module

public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public import CFSG.Sporadic.HNSchreier.SeedsCheckInputs
public import CFSG.Sporadic.HNSchreier.FAData
public meta import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheckInputs
public meta import CFSG.Sporadic.HNSchreier.FAData

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.HN3

open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier
  CFSG.Sporadic.HNSchreier.Native

@[expose] def g3Mat (A B : Array (Array Nat)) : Array (Array Nat) :=
  let regs := progRegsM (initRegsM A B) Data.subgroupProgram
  let hs := extendStrongM #[regs[1]!, regs[2]!] LocalData.strongWords
  mulM 5 133 (wordM (seedSel A B) FAData.g3Root) (mword hs.1 hs.2 FAData.g3H)

@[noinline, expose] def g3OrderChecks (A B : Array (Array Nat)) : Bool :=
  let w := powM 5 133 (g3Mat A B) 3
  FAData.g3Root.all (fun l => l == 1 || l == 2) && plettersOK 17 FAData.g3H &&
    powM 5 133 w 10 == idM 133 && notIdM 133 (powM 5 133 w 5) && notIdM 133 (powM 5 133 w 2)

end CFSG.HardMathSupport.Solomon.Coordinator.HN3
