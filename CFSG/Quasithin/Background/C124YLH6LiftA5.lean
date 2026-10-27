module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.C124YLA6Perm

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL.H6

open Equiv Subgroup CFSG.Quasithin.C124.YL.A6

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem eq_one_of_ker_sq {q : Γ →* P6} (hker3 : Nat.card q.ker = 3) {z : Γ} (hz : z ∈ q.ker)
    (h2 : z * z = 1) : z = 1 := by
  have h3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥q.ker) (x := ⟨z, hz⟩)
    rw [hker3] at this
    exact congrArg Subtype.val this
  have e : z = z ^ 3 * (z * z)⁻¹ := by group
  rw [e, h3, h2]
  simp

theorem card_eq_map_mul_inf_ker (q : Γ →* P6) (H : Subgroup Γ) :
    Nat.card H = Nat.card (H.map q) * Nat.card ↥(q.ker ⊓ H) := by
  have h1 : q.ker.relIndex H = Nat.card (H.map q) := Subgroup.relIndex_ker H q
  have h2 := Subgroup.relIndex_mul_card q.ker H
  rw [h1] at h2
  exact h2.symm

theorem orderOf_eq_three {q : Γ →* P6} (hker3 : Nat.card q.ker = 3) {z : Γ} (hz : z ∈ q.ker)
    (hz1 : z ≠ 1) : orderOf z = 3 := by
  have h3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥q.ker) (x := ⟨z, hz⟩)
    rw [hker3] at this
    exact congrArg Subtype.val this
  have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hd) with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hz1
  · exact h

theorem image_klein {q : Γ →* P6} (hker3 : Nat.card q.ker = 3) {K : Subgroup Γ}
    (hK4 : Nat.card K = 4) (hsq : ∀ a ∈ K, a * a = 1) :
    Nat.card (K.map q) = 4 := by
  have hinj : Function.Injective (q.comp K.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h1 : (a : Γ) ∈ q.ker := ha
    have h2 := eq_one_of_ker_sq hker3 h1 (hsq a a.2)
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  have h : (q.comp K.subtype).range = K.map q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hK4]

theorem klein_normalizes {q : Γ →* P6} (hker3 : Nat.card q.ker = 3)
    (hkc : q.ker ≤ Subgroup.center Γ) {K : Subgroup Γ} (hsq : ∀ a ∈ K, a * a = 1) {ν : Γ}
    (hν : ∀ k ∈ K, q ν * q k * (q ν)⁻¹ ∈ K.map q) : ν ∈ Subgroup.normalizer (K : Set Γ) := by
  refine Subgroup.mem_normalizer_fintype fun k hk => ?_
  obtain ⟨k', hk', hqk⟩ := hν k hk
  have h1 : ν * k * ν⁻¹ * k'⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker]
    simp [map_mul, map_inv, hqk]
  have hz := Subgroup.mem_center_iff.1 (hkc h1)
  have hsqk : ν * k * ν⁻¹ * (ν * k * ν⁻¹) = 1 := by
    have := hsq k hk
    calc ν * k * ν⁻¹ * (ν * k * ν⁻¹) = ν * (k * k) * ν⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hk'1 := hsq k' hk'
  have e1 : (ν * k * ν⁻¹ * k'⁻¹) * (ν * k * ν⁻¹ * k'⁻¹) = 1 := by
    have hc : ∀ g, g * (ν * k * ν⁻¹ * k'⁻¹) = (ν * k * ν⁻¹ * k'⁻¹) * g := fun g => hz g
    calc (ν * k * ν⁻¹ * k'⁻¹) * (ν * k * ν⁻¹ * k'⁻¹)
        = (ν * k * ν⁻¹) * ((k'⁻¹ * (ν * k * ν⁻¹ * k'⁻¹)) ) := by group
      _ = (ν * k * ν⁻¹) * ((ν * k * ν⁻¹ * k'⁻¹) * k'⁻¹) := by rw [hc]
      _ = (ν * k * ν⁻¹ * (ν * k * ν⁻¹)) * (k'⁻¹ * k'⁻¹) := by group
      _ = 1 := by
        rw [hsqk, one_mul]
        have : k'⁻¹ * k'⁻¹ = (k' * k')⁻¹ := by group
        rw [this, hk'1]
        simp
  have h2 := eq_one_of_ker_sq hker3 h1 e1
  have : ν * k * ν⁻¹ = k' := by
    have := congrArg (· * k') h2
    simpa using this
  rw [this]
  exact hk'

end CFSG.Quasithin.C124.YL.H6
