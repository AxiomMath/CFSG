module

public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
import CFSG.RankThree.PartTwo.KFacts.K72List
import CFSG.RankThree.PartTwo.KFacts.K72L3Group
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.GorensteinWalter

theorem three_mul_dvd_sl2_cube (a : ℕ) :
    3 * (a * (a ^ 2 - 1)) ∣ a ^ 3 * ((a ^ 3) ^ 2 - 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have h3 : 3 ∣ a ^ 2 * (a ^ 4 + a ^ 2 + 1) := by
    by_cases h : a % 3 = 0
    · exact Dvd.dvd.mul_right (Dvd.dvd.pow (Nat.dvd_of_mod_eq_zero h) two_ne_zero) _
    · exact Dvd.dvd.mul_left (three_dvd_pow_four_add_sq_add_one h) _
  obtain ⟨m, hm⟩ := h3
  refine ⟨m, ?_⟩
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have h6 : 1 ≤ (a ^ 3) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ ha)
  have hm' : ((a : ℤ) ^ 2 * (a ^ 4 + a ^ 2 + 1)) = 3 * m := by exact_mod_cast hm
  zify [h2, h6]
  linear_combination ((a : ℤ) * (a ^ 2 - 1)) * hm'

theorem isQuasisimple_psl2_of_four_le_card {F : Type*} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) : CFSG.IsQuasisimple (PSL2 F) := by
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (1 : PSL2 F)
  have hxc : x ∈ Subgroup.center (PSL2 F) := Subgroup.mem_center_iff.mpr fun g => h g x
  rw [psl2_center_eq_bot F, Subgroup.mem_bot] at hxc
  exact hx hxc

section Fixed

variable {K : Type} [Field K] [Finite K]

theorem card_center_sl2_subfield (S : Subfield K) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) S)) =
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  by_cases h : (-1 : K) = 1
  · have hS : (-1 : S) = 1 := Subtype.ext (by simpa using h)
    rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one hS,
      CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one h]
  · have hS : (-1 : S) ≠ 1 := fun h' => h (by simpa using congrArg Subtype.val h')
    rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hS,
      CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one h]

theorem three_mul_card_psl2_subfield_dvd (S : Subfield K) {q₀ : ℕ} (hS : Nat.card S = q₀)
    (hK : Nat.card K = q₀ ^ 3) : 3 * Nat.card (PSL2 S) ∣ Nat.card (PSL2 K) := by
  have hSc := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := S)
  have hKc := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
  rw [card_center_sl2_subfield S, hS] at hSc
  rw [hK] at hKc
  have hc : 0 < Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := Nat.card_pos
  apply Nat.dvd_of_mul_dvd_mul_right hc
  rw [mul_assoc, hSc, hKc]
  exact three_mul_dvd_sl2_cube q₀

theorem card_fixedField_of_orderOf_eq_three {σ : K ≃+* K} (hσ3 : orderOf σ = 3) {q₀ : ℕ}
    (hK : Nat.card K = q₀ ^ 3) : Nat.card (GH74.GLS.IVK.fixedField σ) = q₀ := by
  have h := GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσ3, hK] at h
  exact Nat.pow_left_injective (by norm_num) h

theorem exists_eqLocus_mulEquiv_psl2 {α : MulAut (PSL2 K)} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K)) ≃*
        PSL2 (GH74.GLS.IVK.fixedField σ)) := by
  obtain ⟨σ, hσ3, d, hd⟩ :=
    exists_fixed_iff_of_isField (isField_of_pow_three_of_not_inner hα3 hout) hα3
  refine ⟨σ, hσ3, ?_⟩
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K))).map
      (d⁻¹ : MulAut (PSL2 K)).toMonoidHom = (GH74.GLS.IVK.pslIncl σ).range := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hd y).mp hy
    · intro hz
      refine ⟨d z, (hd (d z)).mpr ?_, MulAut.inv_apply_self _ d z⟩
      rwa [MulAut.inv_apply_self]
  exact ⟨(MulEquiv.subgroupMap (d⁻¹ : MulAut (PSL2 K)) _).trans
    ((MulEquiv.subgroupCongr hmap).trans
      (MonoidHom.ofInjective (GH74.GLS.IVK.pslIncl_injective σ)).symm)⟩

end Fixed

theorem fixedPoints_facts_psl2 {K : Type} [Field K] [Finite K] {q₀ : ℕ} (hq₀ : 4 ≤ q₀)
    (hK : Nat.card K = q₀ ^ 3) {α : MulAut (PSL2 K)} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K))) = ⊥ ∧
      CFSG.IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K))) ∧
      3 ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K))) ∧
      3 * Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K))) ∣ Nat.card (PSL2 K) := by
  obtain ⟨σ, hσ3, ⟨e⟩⟩ := exists_eqLocus_mulEquiv_psl2 hα3 hout
  have hF : Nat.card (GH74.GLS.IVK.fixedField σ) = q₀ :=
    card_fixedField_of_orderOf_eq_three hσ3 hK
  have hcard := Nat.card_congr e.toEquiv
  refine ⟨CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e (psl2_center_eq_bot _),
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2
      (isQuasisimple_psl2_of_four_le_card (by rw [hF]; exact hq₀)), ?_, ?_⟩
  · rw [hcard]
    exact three_dvd_card_psl2 _
  · rw [hcard]
    exact three_mul_card_psl2_subfield_dvd _ hF hK

theorem fixedPoints_facts_of_mulEquiv_psl2 {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (e : X ≃* PSL2 K) {q₀ : ℕ} (hq₀ : 4 ≤ q₀) (hK : Nat.card K = q₀ ^ 3) {α : MulAut X}
    (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥ ∧
      CFSG.IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∧
      3 ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∧
      3 * Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∣ Nat.card X := by
  set β := MulAut.congr e α with hβ
  obtain ⟨h1, h2, h3, h4⟩ := fixedPoints_facts_psl2 hq₀ hK (α := β)
    (by rw [hβ, ← map_pow, hα3, map_one]) (by rwa [hβ, isInnerAut_congr])
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id X)).map e.toMonoidHom =
      β.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K)) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : α y = y := hy
      show e (α (e.symm (e y))) = e y
      rw [MulEquiv.symm_apply_apply, hy']
    · intro hz
      have hz' : e (α (e.symm z)) = z := hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      show α (e.symm z) = e.symm z
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact hz'
  let f : α.toMonoidHom.eqLocus (MonoidHom.id X) ≃*
      β.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K)) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  have hcard := Nat.card_congr f.toEquiv
  refine ⟨CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv f h1,
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr f).2 h2, ?_, ?_⟩
  · rw [hcard]
    exact h3
  · rw [hcard, Nat.card_congr e.toEquiv]
    exact h4

end CFSG.RankThree.PartTwo.KFacts
