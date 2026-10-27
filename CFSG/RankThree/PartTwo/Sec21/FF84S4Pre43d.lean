module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreAssemble
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43c
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42d

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

@[expose] def S43_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → CommTheta b b₁ b₂ ∧ Odd (Nat.card (Opp 3 (Cen b)))

theorem S43_odd_of_rest
    (hrest : S43_rest) :
    S43_odd := fun G _ _ b L B K b₁ b₂ h =>
  S43_odd_of_X_odd (a8Model_of_hyp h.hyp) h (hrest G b L B K b₁ b₂ h).1
    (S42_theta_odd (a8Model_of_hyp h.hyp) h) (hrest G b L B K b₁ b₂ h).2

open CFSG.Assembly (InCatalog) in
@[expose] def LemmaSzAut3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup H → (∃ x y : H, x * y ≠ y * x) →
    KCore.KGroupNonab InCatalog H → ¬ 3 ∣ Nat.card H →
    ∀ (Q : Type) [Group Q] [Finite Q], Group.IsPerfect Q →
      IsSimpleGroup (Q ⧸ Subgroup.center Q) →
      (∃ x y : Q ⧸ Subgroup.center Q, x * y ≠ y * x) →
      3 ∣ Nat.card (Q ⧸ Subgroup.center Q) → ∀ φ : Q →* MulAut H, φ = 1

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
