module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1920Force
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1920ForceAltTen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1920ForceThreeA6
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1920ForceShapeFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

theorem false_of_shape19_16_124_of_force {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    (hsh : Shape19_16_124 X Y)
    (h1 : ∀ P : Subgroup X, IsPGroup 3 P → ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x)
    (h3 : ∃ Nn : Subgroup X, Nn ≤ Y ∧ (Nn.subgroupOf Y).Normal ∧ 3 ∣ Nat.card Nn ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3) :
    False := by
  rcases hsh with ⟨halt, _⟩ | ⟨ha6, _⟩ | ⟨m, hm, hsh4⟩
  · obtain ⟨P, hP, x, hx, y, hy, hx3, hy3, hxy⟩ :=
      exists_noncommute_three_of_isAlt_ten halt
    exact hxy (h1 P hP x hx y hy hx3 hy3)
  · obtain ⟨P, hP, x, hx, y, hy, hx3, hy3, hxy⟩ :=
      exists_noncommute_three_of_isA6ModZ3 ha6
    exact hxy (h1 P hP x hx y hy hx3 hy3)
  · exact not_exists_normal_two_three_of_shape_four hm hsh4 h3

@[expose] def K_19_20_forceLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Q : Type) [Group Q] (Y : Subgroup X),
    CFSG.Open.IsQuasisimple X → CFSG.pCore 2 X = ⊥ → Nonempty (Q ≃* X ⧸ center X) →
    (IsLieTypeOver2 Q ∧ List19_16_5 Q ∧ IsNontrivialParabolic X Y) →
    (∀ P : Subgroup X, IsPGroup 3 P → ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x) →
    ((∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range) →
      center X = ⊥ →
      ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ normalizer (S : Set X) ≤ Y) →
    (∃ Nn : Subgroup X, Nn ≤ Y ∧ (Nn.subgroupOf Y).Normal ∧ 3 ∣ Nat.card Nn ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3) →
    CFSG.Blueprint.LieModel X .PSL 3 2 1

theorem k_19_20_force_of_lie (h : K_19_20_forceLie) : K_19_20_force := by
  intro X _ _ Q _ Y hQ hcore hquot hshape h1 h2 h3
  rcases hshape with h124 | hLie
  · exact (false_of_shape19_16_124_of_force h124 h1 h3).elim
  · exact h X Q Y hQ hcore hquot hLie h1 h2 h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
