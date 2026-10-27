module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs

public section

namespace CFSG.CGT.Foote82.Proof511.McLSyl

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.ClassicalInvolution.McLData
  CFSG.ClassicalInvolution.McLProof

@[expose] def sqOneCount (_ : Unit := ()) : Nat :=
  (mulClosureH 275 sgens.toArray capK).1.toList.countP fun T => invoOK 275 T

end CFSG.CGT.Foote82.Proof511.McLSyl
