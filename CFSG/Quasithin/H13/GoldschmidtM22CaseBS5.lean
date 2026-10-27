module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13.GM22

open Equiv

theorem perm5_isSwap_of_odd_involution {σ : Perm (Fin 5)} (h2 : σ * σ = 1)
    (hs : Perm.sign σ = -1) : σ.IsSwap := by
  have key : ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ = -1 →
      ∃ x y : Fin 5, x ≠ y ∧ σ = swap x y := by
    decide +kernel
  obtain ⟨x, y, hxy, h⟩ := key σ h2 hs
  exact ⟨x, y, hxy, h⟩

theorem perm5_normal_eq_top (K : Subgroup (Perm (Fin 5))) [K.Normal] {τ : Perm (Fin 5)}
    (hτ : τ ∈ K) (h2 : τ * τ = 1) (hs : Perm.sign τ = -1) : K = ⊤ := by
  obtain ⟨x, y, hxy, rfl⟩ := perm5_isSwap_of_odd_involution h2 hs
  rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨a, b, hab, rfl⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_swap hxy hab)
  rw [← hc]
  exact Subgroup.Normal.conj_mem inferInstance _ hτ c

theorem perm5_eq_alternating_of_normal (K : Subgroup (Perm (Fin 5))) [K.Normal]
    (hK : K ≤ alternatingGroup (Fin 5)) (hne : K ≠ ⊥) : K = alternatingGroup (Fin 5) := by
  have hn : (K.subgroupOf (alternatingGroup (Fin 5))).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 5)))
    with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have := (Subgroup.mem_subgroupOf (H := K) (K := alternatingGroup (Fin 5))
      (h := ⟨x, hK hx⟩)).mpr hx
    rw [h] at this
    simpa using this
  · refine le_antisymm hK ?_
    intro x hx
    have : (⟨x, hx⟩ : alternatingGroup (Fin 5)) ∈ K.subgroupOf (alternatingGroup (Fin 5)) := by
      rw [h]; trivial
    exact this

theorem card_dvd_eight_of_isPGroup (R : Subgroup (Perm (Fin 5))) (hR : IsPGroup 2 R) :
    Nat.card R ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  have h120 : Nat.card R ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card R
    rwa [Nat.card_eq_fintype_card (α := Perm (Fin 5)), Fintype.card_perm, Fintype.card_fin] at this
  rw [hn] at h120 ⊢
  by_contra hne
  have : 4 ≤ n := by
    by_contra hlt
    exact hne (by interval_cases n <;> norm_num)
  have h16 : 2 ^ 4 ∣ 120 := (pow_dvd_pow 2 this).trans h120
  norm_num at h16

theorem exists_cover_two {H : Type*} [Group H] [Finite H] (K R : Subgroup H) (hKR : K ≤ R)
    (h : Nat.card R ≤ 2 * Nat.card K) : ∃ r₀ ∈ R, ∀ r ∈ R, r ∈ K ∨ r₀⁻¹ * r ∈ K := by
  have h1 := Subgroup.relIndex_mul_card (H := K) (K := R)
  rw [inf_eq_left.mpr hKR] at h1
  have hK : 0 < Nat.card K := Nat.card_pos
  have hle : K.relIndex R ≤ 2 := by
    by_contra hlt
    have : 3 * Nat.card K ≤ K.relIndex R * Nat.card K :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hne : K.relIndex R ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain h2 | h2 : K.relIndex R = 1 ∨ K.relIndex R = 2 := by omega
  · exact ⟨1, R.one_mem, fun r hr => Or.inl (Subgroup.relIndex_eq_one.mp h2 hr)⟩
  · obtain ⟨a, haR, ha⟩ := Subgroup.relIndex_eq_two_iff'.mp h2
    refine ⟨a⁻¹, R.inv_mem haR, fun r hr => ?_⟩
    rcases ha r hr with h3 | h3
    · exact Or.inr (by simpa using h3.1)
    · exact Or.inl h3.1

end CFSG.Quasithin.H13.GM22
