module

public import CFSG.Sporadic.SuzOddCore.SylowCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.SylowCheckInputs

public section

namespace CFSG.ComponentClassification.Walter86.IRRSuz

open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native

@[expose] def commT (a b : Tab) : Bool := comp 1782 a b == comp 1782 b a

@[expose] def zWitOK (z b₁ b₂ : Tab) : Bool :=
  commT b₁ z && commT b₂ z && commT b₁ b₂ && !(b₁ == z) && !(b₂ == z) && !(b₂ == b₁) &&
    !(b₂ == comp 1782 z b₁)

@[expose] def witOK (z y zy b : Tab) : Bool :=
  commT b z && commT b y && !(b == y) && !(b == z) && !(b == zy)

@[expose] def irrCheckWith (T : Array Tab) (z : Tab) (gens : Array Tab) (L : Array Level)
    (base : Array Nat) : Bool :=
  let W := T.filter fun t => isInvTab t && siftA 1782 L base 0 t
  isInvTab z && siftA 1782 L base 0 z && gens.all (fun g => commT z g) &&
    W.any (fun b₁ => W.any fun b₂ => zWitOK z b₁ b₂) &&
    T.all fun y => !isInvTab y || y == z ||
      let zy := comp 1782 z y
      W.any fun b => witOK z y zy b

@[expose] def suzIrrCheck : Bool :=
  irrCheckWith sylowEnum.tabs (invFusionRepArr 19) invSylowArrs smallLevels smallBaseNat.toArray

end CFSG.ComponentClassification.Walter86.IRRSuz
