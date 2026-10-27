module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalField

import CFSG.Quasithin.Recognition.St84.Gen.SL2InnerAut
import CFSG.ClassicalGroups.PCoreSection
import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.PCoreSection CFSG.LieType.BorelTits CFSG.Quasithin.F1
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private def uSL' {F : Type*} [Field F] (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem alpha_one_zero_of_normalizes {L S : Subgroup G} {F : Type*} [Field F]
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    {d : ↥L} (hd : (d : G) ∈ Subgroup.normalizer (S : Set G)) :
    (α d : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨s₁, hs₁⟩ := hα (uSL' 1)
  have hs₁S : (s₁ : G) ∈ S := (hmem s₁).mpr ⟨1, by rw [hs₁]; rfl⟩
  have hconjS : ((d * s₁ * d⁻¹ : ↥L) : G) ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hd _).mp hs₁S
  obtain ⟨t, ht⟩ := (hmem (d * s₁ * d⁻¹)).mp hconjS
  rw [map_mul, map_mul, map_inv, hs₁] at ht
  have h10 := congrFun (congrFun ht 1) 0
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] at h10
  simp [uSL', Matrix.mul_apply, Fin.sum_univ_two] at h10
  have hsq : (α d : Matrix (Fin 2) (Fin 2) F) 1 0 * (α d : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    linear_combination -h10
  exact mul_self_eq_zero.mp hsq

variable {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qLocalData.exists_inner_borelOf_left (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    ∀ d ∈ borelOf L1 S, ∃ g ∈ L2, ∀ x ∈ L2, d * x * d⁻¹ * (g * x * g⁻¹)⁻¹ ∈ pCoreOf 2 L2 := by
  classical
  intro d hd
  obtain ⟨F, hFfield, hFfin, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  obtain ⟨K, hKfield, hKfin, ⟨c₂⟩⟩ := hD.exists_coordRight hH hS
  letI := hFfield
  letI := hKfield
  letI := hKfin
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₂.card])
  obtain ⟨ρ, κ, -, -, -, -, hA, -, -⟩ := hD.exists_ringHom_field hH hS c₁ c₂
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hdL1 : d ∈ L1 := borelOf_le L1 S hd
  have hdS : d ∈ Subgroup.normalizer (S : Set G) := by
    have h := borelOf_le_normalizer L1 S hd
    rwa [inf_eq_left.mpr hSL1] at h
  have hdL2 : d ∈ Subgroup.normalizer (L2 : Set G) := hH.h2.borel_le hd
  have hdQ2 : d ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L2 hdL2
  have hD10 : (c₁.α ⟨d, hdL1⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    alpha_one_zero_of_normalizes c₁.α c₁.surjective_α c₁.mem_iff (d := ⟨d, hdL1⟩) hdS
  have hD11 : (c₁.α ⟨d, hdL1⟩ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h0
    have hdet := (c₁.α ⟨d, hdL1⟩).2
    rw [Matrix.det_fin_two, hD10, h0] at hdet
    simp at hdet
  have hν : ρ ((c₁.α ⟨d, hdL1⟩ : Matrix (Fin 2) (Fin 2) F) 1 1) ≠ 0 :=
    (map_ne_zero ρ).mpr hD11
  refine exists_inner_of_unitriangular c₂.α c₂.surjective_α c₂.eq_one_iff hdL2 hdQ2 hν ?_
  intro s
  obtain ⟨x, hxQ1, hxα⟩ := c₂.exists_pCoreOf_left hH hD hS s
  have hdx1 : d * x * d⁻¹ ∈ pCoreOf 2 L1 := conj_mem_pCoreOf hdL1 hxQ1
  have hdx2 : d * x * d⁻¹ ∈ L2 := (Subgroup.mem_normalizer_iff.mp hdL2 x).mp x.2
  refine ⟨x, ⟨d * x * d⁻¹, hdx2⟩, rfl, hxα, ?_⟩
  obtain ⟨t, ht⟩ := (c₂.mem_iff ⟨_, hdx2⟩).mp (hH.pCoreOf_le_left hdx1)
  have hrow : Multiplicative.toAdd (c₁.β ⟨d * x * d⁻¹, hdx1⟩) 1 =
      (c₁.α ⟨d, hdL1⟩ : Matrix (Fin 2) (Fin 2) F) 1 1 •
        Multiplicative.toAdd (c₁.β ⟨x, hxQ1⟩) 1 := by
    rw [c₁.equivariant ⟨d, hdL1⟩ ⟨x, hxQ1⟩ ⟨_, hdx1⟩ rfl]
    funext j
    simp [Matrix.mul_apply, Fin.sum_univ_two, hD10]
  have h := hA x hxQ1 x.2 (d * x * d⁻¹) hdx1 hdx2 _ hrow
  have hx' : (⟨(x : G), x.2⟩ : ↥L2) = x := rfl
  rw [hx', hxα, ht] at h
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h
  rw [ht, h]

theorem U4qLocalData.exists_inner_borelOf_right (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    ∀ d ∈ borelOf L2 S, ∃ g ∈ L1, ∀ x ∈ L1, d * x * d⁻¹ * (g * x * g⁻¹)⁻¹ ∈ pCoreOf 2 L1 := by
  classical
  intro d hd
  obtain ⟨F, hFfield, hFfin, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  obtain ⟨K, hKfield, hKfin, ⟨c₂⟩⟩ := hD.exists_coordRight hH hS
  letI := hFfield
  letI := hKfield
  letI := hFfin
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hD.one_le, c₂.card⟩
  obtain ⟨ρ, κ, hκ, -, -, hρsurj, -, -, hC⟩ := hD.exists_ringHom_field hH hS c₁ c₂
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hdL2 : d ∈ L2 := borelOf_le L2 S hd
  have hdS : d ∈ Subgroup.normalizer (S : Set G) := by
    have h := borelOf_le_normalizer L2 S hd
    rwa [inf_eq_left.mpr hSL2] at h
  have hdL1 : d ∈ Subgroup.normalizer (L1 : Set G) := hH.h1.borel_le hd
  have hdQ1 : d ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L1 hdL1
  have hA10 : (c₂.α ⟨d, hdL2⟩ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    alpha_one_zero_of_normalizes c₂.α c₂.surjective_α c₂.mem_iff (d := ⟨d, hdL2⟩) hdS
  set a := (c₂.α ⟨d, hdL2⟩ : Matrix (Fin 2) (Fin 2) K) 1 1 with ha_def
  have ha0 : a ≠ 0 := by
    intro h0
    have hdet := (c₂.α ⟨d, hdL2⟩).2
    rw [Matrix.det_fin_two, hA10, ← ha_def, h0] at hdet
    simp at hdet
  have hN : (a * a ^ 2 ^ f) ^ 2 ^ f = a * a ^ 2 ^ f := by
    have hbb := hU.bar_bar a
    rw [hU.bar_apply, hU.bar_apply] at hbb
    rw [mul_pow, hbb, mul_comm]
  obtain ⟨ν, hν⟩ := hρsurj _ hN
  have hN0 : a * a ^ 2 ^ f ≠ 0 := mul_ne_zero ha0 (pow_ne_zero _ ha0)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [map_zero] at hν
    exact hN0 hν.symm
  refine exists_inner_of_unitriangular c₁.α c₁.surjective_α c₁.eq_one_iff hdL1 hdQ1 hν0 ?_
  intro s
  obtain ⟨x, hxQ2, hxα⟩ := c₁.exists_pCoreOf_right hH hD hS s
  have hdx2 : d * x * d⁻¹ ∈ pCoreOf 2 L2 := conj_mem_pCoreOf hdL2 hxQ2
  have hdx1 : d * x * d⁻¹ ∈ L1 := (Subgroup.mem_normalizer_iff.mp hdL1 x).mp x.2
  refine ⟨x, ⟨d * x * d⁻¹, hdx1⟩, rfl, hxα, ?_⟩
  obtain ⟨t, ht⟩ := (c₁.mem_iff ⟨_, hdx1⟩).mp (hH.pCoreOf_le_right hdx2)
  have h11 : Multiplicative.toAdd (c₂.β ⟨d * x * d⁻¹, hdx2⟩) 1 1 =
      a * Multiplicative.toAdd (c₂.β ⟨x, hxQ2⟩) 1 1 * a ^ 2 ^ f := by
    rw [c₂.equivariant ⟨d, hdL2⟩ ⟨x, hxQ2⟩ ⟨_, hdx2⟩ rfl]
    have h0 : (0 : K) ^ 2 ^ f = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
    simp [Matrix.mul_apply, Fin.sum_univ_two, hA10, h0, ← ha_def]
  have hC1 := hC x hxQ2 x.2
  have hC2 := hC (d * x * d⁻¹) hdx2 hdx1
  have hx' : (⟨(x : G), x.2⟩ : ↥L1) = x := rfl
  rw [hx', hxα] at hC1
  rw [ht] at hC2
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at hC1 hC2
  have hρ : ρ t = ρ (ν * s) := by
    apply mul_left_cancel₀ hκ
    rw [map_mul, hν, ← hC2, h11, hC1]
    ring
  rw [ht, ρ.injective hρ]

end CFSG.Quasithin.F112R.St84

end
