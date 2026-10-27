module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def NoDoubleComponentGL : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], 5 ≤ r → ∀ (W : Type) [Group W] [Finite W],
    (∀ a b : W, a * b = b * a) → (∀ w : W, w ^ r = 1) →
    (∃ s : Finset W, s.card ≤ 3 ∧ Subgroup.closure (s : Set W) = ⊤) →
    ∀ (Γ T K : Subgroup (MulAut W)) (n : MulAut W), n ∈ Γ → K ≤ Γ → T ≤ Γ →
      (∀ g ∈ Γ, ∀ t ∈ T, g * t * g⁻¹ ∈ T) → Group.IsSolvable T → ¬ 3 ∣ Nat.card T → ⁅K, K⁆ = K →
      ⁅K, K.map (MulAut.conj n).toMonoidHom⁆ ≤ T → K = ⊥

end CFSG.RankThree.PartTwo.KFacts

end
