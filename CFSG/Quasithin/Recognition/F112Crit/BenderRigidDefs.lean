module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.F112Crit

structure IsRigidQuot (K : Type*) [Group K] : Prop where
  rigid : ∀ P : Sylow 2 K, ∃ x : K, x ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) ∧
    ∀ σ : MulAut K,
      (∃ k : ℕ, ∀ y : K,
        y⁻¹ * (σ ^ 2 ^ k) y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)) →
      (∀ m ∈ Subgroup.normalizer ((P : Subgroup K) : Set K),
        σ m ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)) →
      (∀ d ∈ Subgroup.normalizer ((P : Subgroup K) : Set K),
        x⁻¹ * d * x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) →
        ∀ y : K, y⁻¹ * (σ d * d⁻¹) * y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)) →
      ∀ y : K, y⁻¹ * σ y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)

end CFSG.Quasithin.F112Crit

end
