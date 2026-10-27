module

public import CFSG.Quasithin.EmptyFaithful.A38c8Defs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.Quasithin.A38c9

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem outer_card_M24 :
    Nat.card (Outer (NativeSporadic.Carrier .M24)) = 1 := by
  have hinner : inner NativeSporadic.M24 = ⊤ :=
    CFSG.Sporadic.Schreier.inner_eq_top_of_card_le
      CFSG.Sporadic.Schreier.m24_center_eq_bot' CFSG.Sporadic.Schreier.m24_mulAut_card
  show (inner NativeSporadic.M24).index = 1
  rw [hinner]
  exact Subgroup.index_top

theorem outOddM24_holds :
    A38c8.OutOddM24 := by
  unfold A38c8.OutOddM24
  rw [outer_card_M24]
  exact odd_one

theorem sporadicL4Inner_of_j4
    (h : A38c8.J4L4Inner) :
    A38c8.SporadicL4Inner :=
  ⟨outOddM24_holds, h⟩

end CFSG.Quasithin.A38c9
