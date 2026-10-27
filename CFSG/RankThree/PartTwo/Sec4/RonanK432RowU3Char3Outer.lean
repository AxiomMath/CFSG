module

public import CFSG.RankThree.PartTwo.KFacts.K72L3Fix
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.KFacts.AutPSUInner
public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.RankThree.PartTwo.KFacts
open Matrix

namespace U3Char3

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem unitaryScalars_three_eq_bot_of_not_dvd (h : UnitaryFieldData p f K)
    (hq : ¬ 3 ∣ p ^ f + 1) : unitaryScalars h 3 = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [card_unitaryScalars h (by norm_num)]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hq

theorem unitaryProj_three_injective_of_not_dvd (h : UnitaryFieldData p f K)
    (hq : ¬ 3 ∣ p ^ f + 1) : Function.Injective (unitaryProj h 3) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj, unitaryScalars_three_eq_bot_of_not_dvd h hq]

@[expose] noncomputable def unitaryPSUEquivSU_of_not_dvd (h : UnitaryFieldData p f K)
    (hq : ¬ 3 ∣ p ^ f + 1) : unitarySU p f K 3 ≃* unitaryPSU h 3 :=
  MulEquiv.ofBijective (unitaryProj h 3)
    ⟨unitaryProj_three_injective_of_not_dvd h hq, unitaryProj_surjective h 3⟩

theorem center_unitaryPSU_eq_bot_of_not_dvd (h : UnitaryFieldData p f K) (hq : ¬ 3 ∣ p ^ f + 1)
    (hq2 : 2 < p ^ f) : Subgroup.center (unitaryPSU h 3) = ⊥ :=
  center_eq_bot_of_mulEquiv_of_center_eq_bot (unitaryPSUEquivSU_of_not_dvd h hq).symm
    (by rw [center_unitarySU_three (h := h) hq2, unitaryScalars_three_eq_bot_of_not_dvd h hq])

theorem isInnerAut_of_mem_psuConj_range_of_mod (h : UnitaryFieldData p f K)
    (hq : (p ^ f + 1) % 3 = 1) {β : MulAut (unitaryPSU h 3)} (hβ : β ∈ (psuConj h).range) :
    IsInnerAut β := by
  obtain ⟨A, rfl⟩ := hβ
  set d : Kˣ := GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hd1 : d ^ (p ^ f + 1) = 1 := det_pow_succ_eq_one_of_mem_unitaryIsom3 h A.2
  obtain ⟨m, hm⟩ : ∃ m, p ^ f + 1 = 3 * m + 1 := ⟨(p ^ f + 1) / 3, by omega⟩
  set u : Kˣ := d⁻¹ ^ m with hu
  have hu3 : u ^ 3 = d := by
    have h1 : d⁻¹ ^ (3 * m + 1) = 1 := by rw [← hm, inv_pow, hd1, inv_one]
    rw [pow_succ, mul_eq_one_iff_eq_inv, inv_inv] at h1
    rw [hu, ← pow_mul, mul_comm]
    exact h1
  have hun : u ^ (p ^ f + 1) = 1 := by
    rw [hu, ← pow_mul, mul_comm, pow_mul, inv_pow, hd1, inv_one, one_pow]
  exact psuConj_mem_range_conj_of_det_eq_pow
    (by rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hun, Units.val_one]) hu3.symm

theorem suField_eq_of_psuField_mk_eq_of_not_dvd (h : UnitaryFieldData p f K)
    (hq : ¬ 3 ∣ p ^ f + 1) (σ : K ≃+* K) {g : unitarySU p f K 3}
    (hg : psuField h σ (g : unitaryPSU h 3) = (g : unitaryPSU h 3)) : suField h σ g = g := by
  rw [psuField_mk] at hg
  exact unitaryProj_three_injective_of_not_dvd h hq hg

theorem mem_range_unitaryProj_comp_suIncl_iff_of_not_dvd (h : UnitaryFieldData p f K)
    (hq : ¬ 3 ∣ p ^ f + 1) {σ : K ≃+* K} {f₀ : ℕ} (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ)) (y : unitaryPSU h 3) :
    y ∈ ((unitaryProj h 3).comp (suIncl h h₀ (bar_coe_fixedField h hf h₀))).range ↔
      psuField h σ y = y := by
  have hbar := bar_coe_fixedField h hf h₀
  constructor
  · rintro ⟨g₀, rfl⟩
    rw [MonoidHom.comp_apply]
    have hfix := (mem_range_suIncl_iff h h₀ hbar (suIncl h h₀ hbar g₀)).mp ⟨g₀, rfl⟩
    exact (psuField_mk σ _).trans (congrArg (unitaryProj h 3) hfix)
  · intro hy
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 y
    obtain ⟨g₀, hg₀⟩ :=
      (mem_range_suIncl_iff h h₀ hbar g).mpr (suField_eq_of_psuField_mk_eq_of_not_dvd h hq σ hy)
    exact ⟨g₀, by rw [MonoidHom.comp_apply, hg₀]⟩

theorem exists_congr_eq_psuField_of_mod {X : Type} [Group X] (h : UnitaryFieldData p f K)
    (hq : (p ^ f + 1) % 3 = 1) (hq2 : 2 < p ^ f) (e : X ≃* unitaryPSU h 3) {α : MulAut X}
    (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      ∃ τ : X ≃* unitaryPSU h 3, MulAut.congr τ α = psuField h σ := by
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hD : MulAut.congr e α ∉ (psuConj h).range := fun hm =>
    hout ((isInnerAut_congr e α).mp (isInnerAut_of_mem_psuConj_range_of_mod h hq hm))
  obtain ⟨σ, hσ, H, hβH⟩ := unitary_order_three_field_descent hq2 (MulAut.congr e α) hβ3 hD
  refine ⟨σ, hσ, e.trans (psuConj h H)⁻¹, ?_⟩
  rw [congr_trans_mulAut, hβH]
  group

end Unitary

theorem unitaryFieldData_three_three : UnitaryFieldData 3 3 (GaloisField 3 (2 * 3)) :=
  ⟨Nat.prime_three, by norm_num, GaloisField.card 3 (2 * 3) (by norm_num)⟩

end U3Char3

open U3Char3

theorem exists_fix_card_unitary_char_three {K : Type} [Field K] (h : UnitaryFieldData 3 3 K)
    {α : MulAut (unitaryPSU h 3)} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ H : Subgroup (unitaryPSU h 3), (∀ x, x ∈ H ↔ α x = x) ∧ Nat.card H = 6048 := by
  have hq : ¬ 3 ∣ 3 ^ 3 + 1 := by norm_num
  have hq1 : (3 ^ 3 + 1) % 3 = 1 := by norm_num
  have hq2 : 2 < 3 ^ 3 := by norm_num
  obtain ⟨σ, hσ, τ, hτ⟩ := exists_congr_eq_psuField_of_mod h hq1 hq2 (MulEquiv.refl _) hα hout
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData 3 f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h₀.finite
  have hf₀1 : f₀ = 1 := by omega
  subst hf₀1
  have hinj : Function.Injective
      ((unitaryProj h 3).comp (suIncl h h₀ (bar_coe_fixedField h hf h₀))) :=
    (unitaryProj_three_injective_of_not_dvd h hq).comp (suIncl_injective h h₀ _)
  obtain ⟨eC⟩ := nonempty_eqLocus_mulEquiv τ α _ hinj fun y => by
    rw [hτ]
    exact mem_range_unitaryProj_comp_suIncl_iff_of_not_dvd h hq hf h₀ y
  refine ⟨α.toMonoidHom.eqLocus (MonoidHom.id _), fun x => Iff.rfl, ?_⟩
  rw [Nat.card_congr eC.toEquiv, card_unitarySU_three h₀]
  norm_num

theorem outerRow_unitaryPSU_gf_twentyseven :
    OuterRow (unitaryPSU unitaryFieldData_three_three 3) := by
  have hq : ¬ 3 ∣ 3 ^ 3 + 1 := by norm_num
  refine outerRow_of_fixed_card_dvd
    (center_unitaryPSU_eq_bot_of_not_dvd unitaryFieldData_three_three hq (by norm_num))
    fun α hα hout => ?_
  obtain ⟨H, hH, hcard⟩ := exists_fix_card_unitary_char_three unitaryFieldData_three_three hα hout
  refine ⟨H, 6048, hH, ⟨1, by rw [hcard, mul_one]⟩, ?_⟩
  rw [← Nat.card_congr (unitaryPSUEquivSU_of_not_dvd unitaryFieldData_three_three hq).toEquiv,
    card_unitarySU_three unitaryFieldData_three_three]
  norm_num

end CFSG.RankThree.PartTwo.Sec4.RonanK432
