module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FLinFix
public import CFSG.RankThree.PartTwo.KFacts.K71SU3

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix
open scoped commutatorElement

section FixU

variable {p f f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {σ : K ≃+* K}
  (h₀ : UnitaryFieldData p f₀ (fixedField σ))
  (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))

noncomputable abbrev fixedCoreHomU : unitarySU p f₀ (fixedField σ) 3 →* unitaryPSU h 3 :=
  (unitaryProj h 3).comp (suIncl h h₀ hbar)

noncomputable abbrev fixedCoreU : Subgroup (unitaryPSU h 3) :=
  (fixedCoreHomU h h₀ hbar).range

variable {h h₀ hbar}

theorem fixedCoreU_fixed {y : unitaryPSU h 3} (hy : y ∈ fixedCoreU h h₀ hbar) :
    psuField h σ y = y := by
  obtain ⟨g, rfl⟩ := hy
  change psuField h σ (unitaryProj h 3 (suIncl h h₀ hbar g)) = unitaryProj h 3 (suIncl h h₀ hbar g)
  rw [show unitaryProj h 3 (suIncl h h₀ hbar g) = ((suIncl h h₀ hbar g : unitarySU p f K 3) :
    unitaryPSU h 3) from rfl, psuField_mk,
    (mem_range_suIncl_iff h h₀ hbar _).mp ⟨g, rfl⟩]

theorem exists_scalar_of_psuField_fixed {A : unitarySU p f K 3}
    (hA : psuField h σ (A : unitaryPSU h 3) = (A : unitaryPSU h 3)) :
    ∃ s ∈ unitaryScalars h 3, suField h σ A = A * s := by
  rw [psuField_mk] at hA
  refine ⟨A⁻¹ * suField h σ A, QuotientGroup.eq.mp hA.symm, ?_⟩
  group

theorem commutator_mem_fixedCoreU {y z : unitaryPSU h 3} (hy : psuField h σ y = y)
    (hz : psuField h σ z = z) : ⁅y, z⁆ ∈ fixedCoreU h h₀ hbar := by
  obtain ⟨A, rfl⟩ := unitaryProj_surjective h 3 y
  obtain ⟨B, rfl⟩ := unitaryProj_surjective h 3 z
  obtain ⟨s, hs, hAs⟩ := exists_scalar_of_psuField_fixed hy
  obtain ⟨t, ht, hBt⟩ := exists_scalar_of_psuField_fixed hz
  have hcomm : suField h σ ⁅A, B⁆ = ⁅A, B⁆ := by
    rw [map_commutatorElement, hAs, hBt]
    exact commutatorElement_mul_central (unitaryScalars_le_center h 3 hs)
      (unitaryScalars_le_center h 3 ht) A B
  obtain ⟨C, hC⟩ := (mem_range_suIncl_iff h h₀ hbar _).mpr hcomm
  refine ⟨C, ?_⟩
  change unitaryProj h 3 (suIncl h h₀ hbar C) = ⁅unitaryProj h 3 A, unitaryProj h 3 B⁆
  rw [hC, map_commutatorElement]

theorem ker_fixedCoreHomU (hq : 2 < p ^ f) (hq₀ : 2 < p ^ f₀) :
    (fixedCoreHomU h h₀ hbar).ker = Subgroup.center (unitarySU p f₀ (fixedField σ) 3) := by
  ext g
  rw [MonoidHom.mem_ker]
  change unitaryProj h 3 (suIncl h h₀ hbar g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, ker_unitaryProj]
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro x
    apply suIncl_injective h h₀ hbar
    have hc := Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 3 hg) (suIncl h h₀ hbar x)
    rw [map_mul, map_mul]
    exact hc
  · intro hg
    rw [center_unitarySU_three (h := h₀) hq₀] at hg
    obtain ⟨c, hc, hc3, hgc⟩ := hg
    refine ⟨Units.map ((fixedField σ).subtype : fixedField σ →* K) c, ?_, ?_, ?_⟩
    · rw [UnitaryFieldData.norm, Units.coe_map]
      change (c : fixedField σ).val * h.bar (c : fixedField σ).val = 1
      rw [hbar]
      have := congrArg (fun x : fixedField σ => ((x : fixedField σ) : K)) hc
      simpa [UnitaryFieldData.norm] using this
    · rw [← map_pow, hc3, map_one]
    · apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      ext i j
      rw [coe_suIncl_apply]
      have := congrArg (fun X : GL (Fin 3) (fixedField σ) => ((X : Matrix (Fin 3) (Fin 3) _) i j :
        fixedField σ).val) hgc
      simp only [GeneralLinearGroup.coe_scalar] at this
      by_cases hij : i = j
      · subst hij
        simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using this
      · simpa [Matrix.scalar_apply, Matrix.diagonal_apply, hij] using this

theorem isQuasisimple_unitarySU_three' {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) : IsQuasisimple (unitarySU p f K 3) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl
    (by intro hh; simp only [Prod.mk.injEq, true_and] at hh; omega)).1

noncomputable def fixedCoreUEquiv (hq : 2 < p ^ f) (hq₀ : 2 < p ^ f₀) :
    (unitarySU p f₀ (fixedField σ) 3 ⧸ Subgroup.center (unitarySU p f₀ (fixedField σ) 3)) ≃*
      ↥(fixedCoreU h h₀ hbar) :=
  (QuotientGroup.quotientMulEquivOfEq
    (ker_fixedCoreHomU (h₀ := h₀) (hbar := hbar) hq hq₀).symm).trans
      (QuotientGroup.quotientKerEquivRange (fixedCoreHomU h h₀ hbar))

theorem fixedCoreU_isSimpleGroup (hq : 2 < p ^ f) (hq₀ : 2 < p ^ f₀) :
    IsSimpleGroup ↥(fixedCoreU h h₀ hbar) := by
  haveI : IsSimpleGroup (unitarySU p f₀ (fixedField σ) 3 ⧸
      Subgroup.center (unitarySU p f₀ (fixedField σ) 3)) :=
    (isQuasisimple_unitarySU_three' h₀ hq₀).2.1
  exact (fixedCoreUEquiv hq hq₀).symm.isSimpleGroup

theorem not_isSolvable_fixedCoreU (hq : 2 < p ^ f) (hq₀ : 2 < p ^ f₀) :
    ¬ Group.IsSolvable ↥(fixedCoreU h h₀ hbar) := by
  haveI := fixedCoreU_isSimpleGroup (h := h) (h₀ := h₀) (hbar := hbar) hq hq₀
  intro hs
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  obtain ⟨a, b, hab⟩ := (isQuasisimple_unitarySU_three' h₀ hq₀).2.2
  exact hab ((fixedCoreUEquiv (h := h) (h₀ := h₀) (hbar := hbar) hq hq₀).injective
    (by rw [map_mul, map_mul]; exact hcomm _ _))

noncomputable def fixedCoreUEquivPSU (hq : 2 < p ^ f) (hq₀ : 2 < p ^ f₀) :
    ↥(fixedCoreU h h₀ hbar) ≃* unitaryPSU h₀ 3 :=
  (fixedCoreUEquiv hq hq₀).symm.trans (suCenterEquiv h₀ hq₀)

theorem isSolvable_fixedCoreU (hsolv : Group.IsSolvable (unitarySU p f₀ (fixedField σ) 3)) :
    Group.IsSolvable ↥(fixedCoreU h h₀ hbar) :=
  Group.isSolvable_of_surjective (fixedCoreHomU h h₀ hbar).rangeRestrict_surjective

theorem exists_core_of_fieldAutU {X : Type} [Group X] (e : X ≃* unitaryPSU h 3) (β : MulAut X)
    (hβ : MulAut.congr e β = psuField h σ) :
    ∃ Q : Subgroup X, (∀ x ∈ Q, β x = x) ∧ (∀ y z : X, β y = y → β z = z → ⁅y, z⁆ ∈ Q) ∧
      Nonempty (↥(fixedCoreU h h₀ hbar) ≃* ↥Q) := by
  have hfix : ∀ x : X, β x = x ↔ psuField h σ (e x) = e x := by
    intro x
    rw [← hβ]
    change _ ↔ e (β (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply]
    exact ⟨fun h => by rw [h], fun h => e.injective h⟩
  refine ⟨(fixedCoreU h h₀ hbar).map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [hfix]
    simpa using fixedCoreU_fixed hy
  · intro y z hy hz
    refine ⟨⁅e y, e z⁆, commutator_mem_fixedCoreU ((hfix y).mp hy) ((hfix z).mp hz), ?_⟩
    simp [map_commutatorElement]
  · exact ⟨e.symm.subgroupMap (fixedCoreU h h₀ hbar)⟩

end FixU

end CFSG.RankThree.PartTwo.Sec8.Hering418
