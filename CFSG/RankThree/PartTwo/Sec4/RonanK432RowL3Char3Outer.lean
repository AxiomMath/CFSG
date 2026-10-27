module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL3Tools
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.Item434CharThree
open Matrix
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)

theorem nat_card_galoisField_three_three : Nat.card (GaloisField 3 3) = 27 :=
  (GaloisField.card 3 3 (by norm_num)).trans (by norm_num)

section Char3

variable {K : Type} [Field K] [CharP K 3]

theorem scalars_three_eq_bot_char_three : scalars 3 K = ⊥ := by
  rw [scalars_eq_center, center_SL_three_eq_bot K]

theorem proj_three_injective_char_three : Function.Injective (proj 3 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_three_eq_bot_char_three]

theorem isInnerAut_of_mem_linearAutGroup_char_three [Finite K] (hcop : (Nat.card Kˣ).Coprime 3)
    {β : MulAut (projectiveSL 3 K)} (hβ : β ∈ linearAutGroup 3 K) : IsInnerAut β := by
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hβ
  set u : Kˣ := (powCoprime hcop).symm (GeneralLinearGroup.det A) with hu
  have hu3 : u ^ 3 = GeneralLinearGroup.det A := by
    rw [← powCoprime_apply hcop, hu, Equiv.apply_symm_apply]
  exact conjAut_mem_range_conj_of_det_eq_pow hu3.symm

theorem map_eq_of_fieldAut_proj_eq_char_three (σ : K ≃+* K)
    {A : SpecialLinearGroup (Fin 3) K} (h : fieldAut 3 K σ (proj 3 K A) = proj 3 K A) :
    SpecialLinearGroup.map σ.toRingHom A = A := by
  rw [fieldAut_proj] at h
  exact proj_three_injective_char_three h

theorem mem_range_proj_comp_map_iff_char_three (σ : K ≃+* K) (y : projectiveSL 3 K) :
    y ∈ ((proj 3 K).comp
        (SpecialLinearGroup.map (CFSG.GH74.GLS.IVK.fixedField σ).subtype)).range ↔
      fieldAut 3 K σ y = y := by
  constructor
  · rintro ⟨A₀, rfl⟩
    rw [MonoidHom.comp_apply, fieldAut_proj]
    congr 1
    ext i j
    exact CFSG.GH74.GLS.IVK.fixedField_apply σ _
  · intro hy
    obtain ⟨A, rfl⟩ := proj_surjective 3 K y
    obtain ⟨A₀, hA₀⟩ := exists_sl_map_subtype_eq (map_eq_of_fieldAut_proj_eq_char_three σ hy)
    exact ⟨A₀, by rw [MonoidHom.comp_apply, hA₀]⟩

theorem exists_congr_eq_fieldAut_char_three [Finite K] {X : Type} [Group X]
    (hcop : (Nat.card Kˣ).Coprime 3) (e : X ≃* projSL 3 K) {α : MulAut X} (hα : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      ∃ τ : X ≃* projectiveSL 3 K, MulAut.congr τ α = fieldAut 3 K σ := by
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 K
  have hβ3 : MulAut.congr (e.trans φ) α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hD : MulAut.congr (e.trans φ) α ∉ linearAutGroup 3 K := fun h =>
    hout ((isInnerAut_congr (e.trans φ) α).mp
      (isInnerAut_of_mem_linearAutGroup_char_three hcop h))
  obtain ⟨σ, hσ, H, hβH⟩ :=
    linear_order_three_field_descent le_rfl (MulAut.congr (e.trans φ) α) hβ3 hD
  refine ⟨σ, hσ, (e.trans φ).trans (conjAut 3 K H)⁻¹, ?_⟩
  rw [congr_trans_mulAut, hβH]
  group

theorem exists_fix_card_char_three [Finite K] (hK : Nat.card K = 27)
    {α : MulAut SL(3, K)} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ H : Subgroup SL(3, K), (∀ x, x ∈ H ↔ α x = x) ∧ Nat.card H = 5616 := by
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units, hK]
    norm_num
  obtain ⟨σ, hσ, τ, hτ⟩ := exists_congr_eq_fieldAut_char_three hcop (slEquivProjSL K) hα hout
  have hinj : Function.Injective
      ((proj 3 K).comp (SpecialLinearGroup.map (CFSG.GH74.GLS.IVK.fixedField σ).subtype)) :=
    proj_three_injective_char_three.comp (sl_map_subtype_injective σ)
  obtain ⟨eH⟩ := nonempty_eqLocus_mulEquiv τ α _ hinj fun y => by
    rw [hτ]
    exact mem_range_proj_comp_map_iff_char_three σ y
  have hF : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) = 3 := by
    have h := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ, hK] at h
    generalize Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) = x at h ⊢
    have hx : x ≤ 3 := by
      by_contra hc
      have hc' : 4 ≤ x := by omega
      have : 4 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hc' 3
      omega
    interval_cases x <;> first | rfl | (norm_num at h)
  refine ⟨α.toMonoidHom.eqLocus (MonoidHom.id _), fun x => ?_, ?_⟩
  · exact Iff.rfl
  · rw [Nat.card_congr eH.toEquiv, card_sl_three_eq, hF]
    norm_num

end Char3

theorem outerRow_SL_three_gf_twentyseven : OuterRow SL(3, GaloisField 3 3) := by
  refine outerRow_of_fixed_card_dvd (center_SL_three_eq_bot (GaloisField 3 3)) fun α hα hout => ?_
  obtain ⟨H, hH, hcard⟩ := exists_fix_card_char_three nat_card_galoisField_three_three hα hout
  refine ⟨H, 5616, hH, ⟨1, by rw [hcard, mul_one]⟩, ?_⟩
  rw [card_sl_three_eq, nat_card_galoisField_three_three]
  norm_num

theorem outerRow_projSL_three_gf_twentyseven : OuterRow (projSL 3 (GaloisField 3 3)) :=
  OuterRow.of_mulEquiv (slEquivProjSL (GaloisField 3 3)) outerRow_SL_three_gf_twentyseven

end CFSG.RankThree.PartTwo.Sec4.RonanK432
