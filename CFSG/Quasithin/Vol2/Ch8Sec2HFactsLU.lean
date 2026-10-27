module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Background.HDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H

@[expose] def HLU82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    ((BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) ∨
      (MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) ∨
      (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) ∨
      (MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3)) →
    CFSG.IsQuasisimple (↥(perfectCore (H ⊓ stabSub (fixV X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabSub (fixV X)))) ∧
      ((BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) ∨
          (MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) →
        AlternatingNatural (V := ↥(fixV X))
          (autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X)) ⊤ ⊥ 5) ∧
      (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7 →
        AlternatingNatural (V := ↥(fixV X))
          (autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X)) ⊤ ⊥ 6) ∧
      (MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3 →
        autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X) = ⊤)

end CFSG.Quasithin.H13
