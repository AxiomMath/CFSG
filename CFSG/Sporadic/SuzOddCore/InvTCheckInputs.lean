
module

public import CFSG.Sporadic.SuzOddCore.InvGraphCheckBase
public import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public meta import CFSG.Sporadic.SuzOddCore.InvGraphCheckBase
public meta import CFSG.Sporadic.SuzOddCore.SmallChainCheck

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def inM (g : Array Nat) : Bool := siftA 1782 smallLevels smallBaseNat.toArray 0 g

@[expose] def fixedCount (t : Array Nat) : Nat :=
  (Finset.univ.filter fun x : Fin 1782 => t[x.val]! = x.val).card

@[expose] def commutesA (g t : Array Nat) : Bool := eqA 1782 (compA 1782 g t) (compA 1782 t g)

end CFSG.Sporadic.SuzOddCore
