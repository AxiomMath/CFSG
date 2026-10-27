module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FLinOT
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3Gen

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix
open scoped commutatorElement

section Fix

variable {F : Type} [Field F]

theorem commutatorElement_mul_central {G : Type*} [Group G] {s t : G}
    (hs : s ∈ Subgroup.center G) (ht : t ∈ Subgroup.center G) (a b : G) :
    ⁅a * s, b * t⁆ = ⁅a, b⁆ := by
  have hs' : ∀ g : G, s * g = g * s := fun g => ((Subgroup.mem_center_iff.mp hs) g).symm
  have ht' : ∀ g : G, t * g = g * t := fun g => ((Subgroup.mem_center_iff.mp ht) g).symm
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev, _root_.mul_inv_rev]
  calc a * s * (b * t) * (s⁻¹ * a⁻¹) * (t⁻¹ * b⁻¹)
      = a * (s * (b * t)) * (s⁻¹ * a⁻¹) * (t⁻¹ * b⁻¹) := by simp only [mul_assoc]
    _ = a * ((b * t) * s) * (s⁻¹ * a⁻¹) * (t⁻¹ * b⁻¹) := by rw [hs' (b * t)]
    _ = a * b * (t * a⁻¹) * (t⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * t) * (t⁻¹ * b⁻¹) := by rw [ht' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

@[expose] noncomputable def fixedCore (σ : F ≃+* F) : Subgroup (projectiveSL 3 F) :=
  ((proj 3 F).comp (SpecialLinearGroup.map (fixedField σ).subtype)).range

theorem fixedCore_fixed {σ : F ≃+* F} {y : projectiveSL 3 F} (hy : y ∈ fixedCore σ) :
    fieldAut 3 F σ y = y := by
  obtain ⟨A, rfl⟩ := hy
  change fieldAut 3 F σ (proj 3 F (SpecialLinearGroup.map (fixedField σ).subtype A)) =
    proj 3 F (SpecialLinearGroup.map (fixedField σ).subtype A)
  rw [fieldAut_proj]
  congr 1
  refine sl_ext ?_
  ext i j
  change σ ((fixedField σ).subtype ((A : Matrix (Fin 3) (Fin 3) (fixedField σ)) i j)) =
    (fixedField σ).subtype ((A : Matrix (Fin 3) (Fin 3) (fixedField σ)) i j)
  exact CFSG.GH74.GLS.IVK.fixedField_apply σ _

theorem exists_scalar_of_fieldAut_fixed {σ : F ≃+* F} {A : SpecialLinearGroup (Fin 3) F}
    (h : fieldAut 3 F σ (proj 3 F A) = proj 3 F A) :
    ∃ s ∈ scalars 3 F, SpecialLinearGroup.map σ.toRingHom A = A * s := by
  rw [fieldAut_proj] at h
  refine ⟨A⁻¹ * SpecialLinearGroup.map σ.toRingHom A, proj_eq_proj_iff.mp h.symm, ?_⟩
  group

theorem commutator_mem_fixedCore {σ : F ≃+* F} {y z : projectiveSL 3 F}
    (hy : fieldAut 3 F σ y = y) (hz : fieldAut 3 F σ z = z) : ⁅y, z⁆ ∈ fixedCore σ := by
  obtain ⟨A, rfl⟩ := proj_surjective 3 F y
  obtain ⟨B, rfl⟩ := proj_surjective 3 F z
  obtain ⟨s, hs, hAs⟩ := exists_scalar_of_fieldAut_fixed hy
  obtain ⟨t, ht, hBt⟩ := exists_scalar_of_fieldAut_fixed hz
  have hcomm : SpecialLinearGroup.map σ.toRingHom ⁅A, B⁆ = ⁅A, B⁆ := by
    rw [map_commutatorElement, hAs, hBt]
    exact commutatorElement_mul_central ((scalars_eq_center 3 F) ▸ hs)
      ((scalars_eq_center 3 F) ▸ ht) A B
  obtain ⟨C, hC⟩ := CFSG.RankThree.PartTwo.KFacts.exists_sl_map_subtype_eq hcomm
  refine ⟨C, ?_⟩
  change proj 3 F (SpecialLinearGroup.map (fixedField σ).subtype C) = ⁅proj 3 F A, proj 3 F B⁆
  rw [hC, map_commutatorElement]

noncomputable abbrev fixedCoreHom (σ : F ≃+* F) :
    SpecialLinearGroup (Fin 3) (fixedField σ) →* projectiveSL 3 F :=
  (proj 3 F).comp (SpecialLinearGroup.map (fixedField σ).subtype)

theorem ker_fixedCoreHom (σ : F ≃+* F) : (fixedCoreHom σ).ker = scalars 3 (fixedField σ) := by
  ext A
  rw [MonoidHom.mem_ker]
  change proj 3 F (SpecialLinearGroup.map (fixedField σ).subtype A) = 1 ↔ _
  rw [proj_eq_one_iff]
  constructor
  · rintro ⟨c, hc, hAc⟩
    rw [Matrix.SpecialLinearGroup.map_apply_coe] at hAc
    have hent : ∀ i j : Fin 3,
        (fixedField σ).subtype ((A : Matrix (Fin 3) (Fin 3) (fixedField σ)) i j) =
          if i = j then (c : F) else 0 := by
      intro i j
      have h := congrFun (congrFun hAc i) j
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using h
    have hdiag : ∀ i : Fin 3, (A : Matrix (Fin 3) (Fin 3) (fixedField σ)) i i =
        (A : Matrix (Fin 3) (Fin 3) (fixedField σ)) 0 0 := by
      intro i
      apply (fixedField σ).subtype.injective
      rw [hent i i, hent 0 0]
      simp
    have hoff : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) (fixedField σ)) i j = 0 := by
      intro i j hij
      apply (fixedField σ).subtype.injective
      rw [hent i j, if_neg hij]
      simp
    have hc0 : (A : Matrix (Fin 3) (Fin 3) (fixedField σ)) 0 0 ≠ 0 := by
      intro h0
      have := hent 0 0
      rw [h0] at this
      simp only [map_zero, if_true] at this
      exact c.ne_zero this.symm
    have hc3 : ((A : Matrix (Fin 3) (Fin 3) (fixedField σ)) 0 0) ^ 3 = 1 := by
      apply (fixedField σ).subtype.injective
      rw [map_pow, hent 0 0, if_pos rfl, map_one, ← Units.val_pow_eq_pow_val, hc]
      simp
    refine ⟨Units.mk0 _ hc0, by
      rw [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_mk0, hc3, Units.val_one], ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hdiag i]
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    · rw [hoff i j hij]
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
  · rintro ⟨c, hc, hAc⟩
    refine ⟨Units.map (fixedField σ).subtype.toMonoidHom c, ?_, ?_⟩
    · rw [← map_pow, hc, map_one]
    · rw [Matrix.SpecialLinearGroup.map_apply_coe, hAc]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply, Matrix.diagonal_apply]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]

noncomputable def fixedCoreEquiv (σ : F ≃+* F) :
    projectiveSL 3 (fixedField σ) ≃* ↥(fixedCore σ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_fixedCoreHom σ).symm).trans
    (QuotientGroup.quotientKerEquivRange (fixedCoreHom σ))

theorem fixedCore_isSimpleGroup (σ : F ≃+* F) : IsSimpleGroup ↥(fixedCore σ) := by
  haveI : IsSimpleGroup (projectiveSL 3 (fixedField σ)) :=
    Sec21.Item223CensusResProof.isSimpleGroup_projectiveSL' (K := fixedField σ) (n := 3) le_rfl
  exact (fixedCoreEquiv σ).symm.isSimpleGroup

theorem not_isSolvable_fixedCore (σ : F ≃+* F) : ¬ Group.IsSolvable ↥(fixedCore σ) := by
  haveI := fixedCore_isSimpleGroup σ
  intro hs
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  obtain ⟨a, b, hab⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_noncomm_projectiveSL_three (K := fixedField σ)
  exact hab ((fixedCoreEquiv σ).injective (by rw [map_mul, map_mul]; exact hcomm _ _))

theorem exists_core_of_fieldAut {X : Type} [Group X] (e : X ≃* projectiveSL 3 F) (β : MulAut X)
    {σ : F ≃+* F} (hβ : MulAut.congr e β = fieldAut 3 F σ) :
    ∃ Q : Subgroup X, (∀ x ∈ Q, β x = x) ∧ (∀ y z : X, β y = y → β z = z → ⁅y, z⁆ ∈ Q) ∧
      IsSimpleGroup ↥Q ∧ ¬ Group.IsSolvable ↥Q ∧
        Nonempty (↥Q ≃* projectiveSL 3 (fixedField σ)) := by
  have hfix : ∀ x : X, β x = x ↔ fieldAut 3 F σ (e x) = e x := by
    intro x
    rw [← hβ]
    change _ ↔ e (β (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply]
    exact ⟨fun h => by rw [h], fun h => e.injective h⟩
  let ε : ↥(fixedCore σ) ≃* ↥((fixedCore σ).map e.symm.toMonoidHom) :=
    e.symm.subgroupMap (fixedCore σ)
  refine ⟨(fixedCore σ).map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [hfix]
    simpa using fixedCore_fixed hy
  · intro y z hy hz
    refine ⟨⁅e y, e z⁆, commutator_mem_fixedCore ((hfix y).mp hy) ((hfix z).mp hz), ?_⟩
    simp [map_commutatorElement]
  · haveI := fixedCore_isSimpleGroup σ
    exact ε.symm.isSimpleGroup
  · intro hs
    exact not_isSolvable_fixedCore σ
      (Group.isSolvable_of_isSolvable_injective (f := ε.toMonoidHom) ε.injective)
  · exact ⟨ε.symm.trans (fixedCoreEquiv σ).symm⟩

end Fix

end CFSG.RankThree.PartTwo.Sec8.Hering418
