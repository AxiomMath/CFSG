module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem conjAut_range_normal [Finite K] (hn : 3 ≤ n) : (conjAut n K).range.Normal := by
  have h := (stdPinnedPSL_stable (n := n) (K := K) hn).normal
  rw [stdPinnedPSL_inndiag, linearAutGroup_eq_range] at h
  exact h

theorem exists_mem_fieldAut_range_of_pow_eq_one [Finite K] (hn : 3 ≤ n) {p : ℕ} (hp2 : Odd p)
    (α : MulAut (projectiveSL n K)) (hα : α ^ p ∈ (conjAut n K).range) :
    ∃ σ : K ≃+* K, α * (fieldAut n K σ)⁻¹ ∈ (conjAut n K).range := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform α
  have : (conjAut n K).range.Normal := conjAut_range_normal hn
  set N := (conjAut n K).range with hN
  set π := QuotientGroup.mk' N with hπ
  have hπ1 : ∀ x : MulAut (projectiveSL n K), π x = 1 ↔ x ∈ N := fun x =>
    QuotientGroup.eq_one_iff x
  obtain ⟨-, -, -, hδδ, -, -, -⟩ := standard_automorphism_transport (n := n) (K := K)
  have hcomm : ∀ τ : K ≃+* K, dualAut n K * fieldAut n K τ = fieldAut n K τ * dualAut n K :=
    fun τ => dualAut_mul_fieldAut τ
  have hπA : π (conjAut n K A) = 1 := (hπ1 _).2 ⟨A, rfl⟩
  have hv2 : π (dualAut n K) * π (dualAut n K) = 1 := by rw [← map_mul, hδδ, map_one]
  have huv : π (fieldAut n K σ) * π (dualAut n K) = π (dualAut n K) * π (fieldAut n K σ) := by
    rw [← map_mul, ← map_mul, hcomm σ]
  obtain ⟨k, hk⟩ := hp2
  have hvp : π (dualAut n K) ^ p = π (dualAut n K) := by
    have hv2' : π (dualAut n K) ^ 2 = 1 := by rw [pow_two]; exact hv2
    rw [hk, pow_succ, pow_mul, hv2', one_pow, one_mul]
  interval_cases ε
  · refine ⟨σ, ?_⟩
    rw [pow_zero, mul_one, mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨A, rfl⟩
  · have hw : π (conjAut n K A * fieldAut n K σ * dualAut n K ^ 1) =
        π (fieldAut n K σ) * π (dualAut n K) := by
      rw [pow_one, map_mul, map_mul, hπA, one_mul]
    have hαp : (π (fieldAut n K σ) * π (dualAut n K)) ^ p = 1 := by
      rw [← hw, ← map_pow]
      exact (hπ1 _).2 hα
    rw [(show Commute (π (fieldAut n K σ)) (π (dualAut n K)) from huv).mul_pow, hvp] at hαp
    have hvu : π (dualAut n K) = (π (fieldAut n K σ) ^ p)⁻¹ := eq_inv_of_mul_eq_one_right hαp
    refine ⟨σ ^ ((1 : ℤ) - p), ?_⟩
    refine (hπ1 _).1 ?_
    rw [map_mul, map_inv, hw, map_zpow, map_zpow, hvu, ← zpow_natCast, ← zpow_neg, ← zpow_one_add,
      ← zpow_neg, ← zpow_add, show (1 + -(p : ℤ) + -(1 - (p : ℤ))) = 0 by ring, zpow_zero]

theorem card_le_of_injective_mod_pgl [Finite K] (hn : 3 ≤ n) {ℓ m : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Type*} [Group E]
    [Finite E] (hE : ∀ e : E, e ^ p = 1) (ρ : E →* MulAut (projectiveSL n K))
    (hinj : ∀ e : E, ρ e ∈ (conjAut n K).range → e = 1) : Nat.card E ≤ p := by
  classical
  have hN : (conjAut n K).range.Normal := conjAut_range_normal hn
  set N := (conjAut n K).range with hNdef
  let π : MulAut (projectiveSL n K) →* MulAut (projectiveSL n K) ⧸ N := QuotientGroup.mk' N
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hℓ K hK).2
  let Fb : Subgroup (MulAut (projectiveSL n K) ⧸ N) := (π.comp (fieldAut n K)).range
  have hFbcyc : IsCyclic Fb :=
    isCyclic_of_surjective (π.comp (fieldAut n K)).rangeRestrict (π.comp (fieldAut n K)).rangeRestrict_surjective
  have hFbmem : ∀ e : E, π (ρ e) ∈ Fb := by
    intro e
    obtain ⟨τ, hτ⟩ := exists_mem_fieldAut_range_of_pow_eq_one hn (hp.eq_two_or_odd'.resolve_left hp2)
      (ρ e) (by rw [← map_pow, hE e, map_one]; exact N.one_mem)
    have h1 : π (ρ e * (fieldAut n K τ)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hτ
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact ⟨τ, by simpa using h1.symm⟩
  let f : E →* Fb := (π.comp ρ).codRestrict Fb hFbmem
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply hinj
    have : π (ρ e) = 1 := congrArg Subtype.val he
    exact (QuotientGroup.eq_one_iff _).1 this
  have : Finite Fb := inferInstance
  let _ : Fintype Fb := Fintype.ofFinite Fb
  have hle := IsCyclic.card_pow_eq_one_le (α := Fb) hp.pos
  calc Nat.card E ≤ Nat.card {x : Fb // x ^ p = 1} := by
        refine Nat.card_le_card_of_injective (fun e => ⟨f e, ?_⟩) ?_
        · rw [← map_pow, hE e, map_one]
        · intro a b hab
          exact hfinj (congrArg Subtype.val hab)
    _ ≤ p := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact hle

end CFSG.RankThree.PartOne.S15K
