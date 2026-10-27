module

public import CFSG.RankThree.PartTwo.KFacts.K72L3Field
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GH74.GLS.IVK (fixedField fixedField_apply fixedField_card_pow)
open Matrix

theorem nonempty_eqLocus_mulEquiv {X Y M : Type*} [Group X] [Group Y] [Group M] (τ : X ≃* Y)
    (α : MulAut X) (ι : M →* Y) (hι : Function.Injective ι)
    (hrange : ∀ y, y ∈ ι.range ↔ MulAut.congr τ α y = y) :
    Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id X) ≃* M) := by
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id X)).map τ.toMonoidHom = ι.range := by
    ext y
    rw [hrange]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change τ (α (τ.symm (τ x))) = τ x
      rw [MulEquiv.symm_apply_apply]
      exact congrArg τ hx
    · intro hy
      refine ⟨τ.symm y, ?_, τ.apply_symm_apply y⟩
      change α (τ.symm y) = τ.symm y
      apply τ.injective
      rw [MulEquiv.apply_symm_apply]
      exact hy
  exact ⟨(Subgroup.equivMapOfInjective _ τ.toMonoidHom τ.injective).trans
    ((MulEquiv.subgroupCongr hmap).trans (MonoidHom.ofInjective hι).symm)⟩

theorem pow_three_mod_three (a : ℕ) : a ^ 3 % 3 = a % 3 := by
  have h : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rw [Nat.pow_mod]
  rcases h with h | h | h <;> rw [h]

section Linear

variable {K : Type} [Field K]

theorem mem_range_proj_comp_map_iff (hK : Nat.card K % 3 = 2) (σ : K ≃+* K)
    (y : projectiveSL 3 K) :
    y ∈ ((proj 3 K).comp (SpecialLinearGroup.map (fixedField σ).subtype)).range ↔
      fieldAut 3 K σ y = y := by
  constructor
  · rintro ⟨A₀, rfl⟩
    rw [MonoidHom.comp_apply, fieldAut_proj]
    congr 1
    ext i j
    exact fixedField_apply σ _
  · intro hy
    obtain ⟨A, rfl⟩ := proj_surjective 3 K y
    obtain ⟨A₀, hA₀⟩ := exists_sl_map_subtype_eq (map_eq_of_fieldAut_proj_eq hK σ hy)
    exact ⟨A₀, by rw [MonoidHom.comp_apply, hA₀]⟩

theorem exists_congr_eq_fieldAut_of_mulEquiv_projSL {X : Type} [Group X] [Finite K]
    (hK : Nat.card K % 3 = 2) (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K)
    {α : MulAut X} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      ∃ τ : X ≃* projectiveSL 3 K, MulAut.congr τ α = fieldAut 3 K σ := by
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 K
  have hβ3 : MulAut.congr (e.trans φ) α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hD : MulAut.congr (e.trans φ) α ∉ linearAutGroup 3 K := fun h =>
    hout ((isInnerAut_congr (e.trans φ) α).mp (isInnerAut_of_mem_linearAutGroup hK h))
  obtain ⟨σ, hσ, H, hβH⟩ :=
    linear_order_three_field_descent le_rfl (MulAut.congr (e.trans φ) α) hβ3 hD
  refine ⟨σ, hσ, (e.trans φ).trans (conjAut 3 K H)⁻¹, ?_⟩
  rw [congr_trans_mulAut, hβH]
  group

theorem fixedPoints_facts_of_mulEquiv_projSL {X : Type} [Group X] [Finite K]
    (hK : Nat.card K % 3 = 2) (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K)
    {α : MulAut X} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥ ∧
      CFSG.IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) := by
  obtain ⟨σ, hσ, τ, hτ⟩ := exists_congr_eq_fieldAut_of_mulEquiv_projSL hK e hα hout
  have hK₀ : Nat.card (fixedField σ) % 3 = 2 := by
    have hcard := fixedField_card_pow σ
    rw [hσ] at hcard
    rw [← pow_three_mod_three, hcard, hK]
  have hinj : Function.Injective
      ((proj 3 K).comp (SpecialLinearGroup.map (fixedField σ).subtype)) :=
    (proj_three_injective hK).comp (sl_map_subtype_injective σ)
  obtain ⟨eC⟩ := nonempty_eqLocus_mulEquiv τ α _ hinj fun y => by
    rw [hτ]
    exact mem_range_proj_comp_map_iff hK σ y
  refine ⟨center_eq_bot_of_mulEquiv_of_center_eq_bot eC ?_,
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv eC.symm
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 (fixedField σ) le_rfl)⟩
  rw [← scalars_eq_center, scalars_three_eq_bot_of_mod_three hK₀]

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem mem_range_unitaryProj_comp_suIncl_iff (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    {σ : K ≃+* K} {f₀ : ℕ} (hf : f = 3 * f₀) (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (y : unitaryPSU h 3) :
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
      (mem_range_suIncl_iff h h₀ hbar g).mpr (suField_eq_of_psuField_mk_eq h hq σ hy)
    exact ⟨g₀, by rw [MonoidHom.comp_apply, hg₀]⟩

theorem exists_congr_eq_psuField_of_mulEquiv_unitaryPSU {X : Type} [Group X]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f)
    (e : X ≃* unitaryPSU h 3) {α : MulAut X} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      ∃ τ : X ≃* unitaryPSU h 3, MulAut.congr τ α = psuField h σ := by
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hD : MulAut.congr e α ∉ (psuConj h).range := fun hm =>
    hout ((isInnerAut_congr e α).mp (isInnerAut_of_mem_psuConj_range h hq hm))
  obtain ⟨σ, hσ, H, hβH⟩ := unitary_order_three_field_descent hq2 (MulAut.congr e α) hβ3 hD
  refine ⟨σ, hσ, e.trans (psuConj h H)⁻¹, ?_⟩
  rw [congr_trans_mulAut, hβH]
  group

theorem fixedPoints_facts_of_mulEquiv_unitaryPSU {X : Type} [Group X]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f)
    (e : X ≃* unitaryPSU h 3) {α : MulAut X} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥ ∧
      CFSG.IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) := by
  obtain ⟨σ, hσ, τ, hτ⟩ := exists_congr_eq_psuField_of_mulEquiv_unitaryPSU h hq hq2 e hα hout
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have : Fact p.Prime := ⟨h.prime⟩
  have := h₀.finite
  have hpow : p ^ f = (p ^ f₀) ^ 3 := by rw [hf, ← pow_mul, mul_comm]
  have hq₀ : p ^ f₀ % 3 = 1 := by rw [← pow_three_mod_three, ← hpow, hq]
  have hq₀2 : 2 < p ^ f₀ := by
    have h2 : 2 ≤ p ^ f₀ := h.prime.two_le.trans (Nat.le_self_pow (by omega) p)
    have h2' : p ^ f₀ ≠ 2 := fun h2 => by rw [h2] at hq₀; norm_num at hq₀
    omega
  have hinj : Function.Injective
      ((unitaryProj h 3).comp (suIncl h h₀ (bar_coe_fixedField h hf h₀))) :=
    (unitaryProj_three_injective h hq).comp (suIncl_injective h h₀ _)
  obtain ⟨eC⟩ := nonempty_eqLocus_mulEquiv τ α _ hinj fun y => by
    rw [hτ]
    exact mem_range_unitaryProj_comp_suIncl_iff h hq hf h₀ y
  have hnq : ((3 : ℕ), p ^ f₀) ≠ (3, 2) := by
    intro h3
    simp only [Prod.mk.injEq, true_and] at h3
    omega
  refine ⟨center_eq_bot_of_mulEquiv_of_center_eq_bot eC ?_,
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv eC.symm
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (by rw [hcard, ← pow_mul, mul_comm]) le_rfl hnq).1⟩
  rw [center_unitarySU_three (h := h₀) hq₀2, unitaryScalars_three_eq_bot_of_mod_three h₀ hq₀]

end Unitary

theorem fixedPoints_facts_of_isoLThreeMinusPi {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 ≤ n) (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) {α : MulAut X} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥ ∧
      CFSG.IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∧
      3 ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id X)) := by
  have h3 : 3 ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id X)) := by
    obtain ⟨-, x₀, -, hx₀, -, hx₀3, hx₀1, -⟩ := fixedData_of_isoLThreeMinusPi hn hX α hα3 hout
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have ho : orderOf (⟨x₀, hx₀⟩ : α.toMonoidHom.eqLocus (MonoidHom.id X)) = 3 :=
      orderOf_eq_prime (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hx₀3))
        (fun h1 => hx₀1 (congrArg Subtype.val h1))
    rw [← ho]
    exact orderOf_dvd_natCard _
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    obtain ⟨hc, hqs⟩ := fixedPoints_facts_of_mulEquiv_unitaryPSU h hq hq2 (e.trans φ.symm) hα3 hout
    exact ⟨hc, hqs, h3⟩
  · obtain ⟨hc, hqs⟩ := fixedPoints_facts_of_mulEquiv_projSL
      (by rwa [GaloisField.card 2 (3 * n) (by omega)]) e hα3 hout
    exact ⟨hc, hqs, h3⟩

end CFSG.RankThree.PartTwo.KFacts
