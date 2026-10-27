module

public import CFSG.LieType.Sp6Spin.Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LieType.D4Small CFSG.LieType.Sp6Spin CFSG.StandardType
  CFSG.StandardType.Triality
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.RankThree.PartOne.AUTSL
open CFSG.SeitzReduction.F4Pilot
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply coe_quadPlus toStdD)
open scoped Matrix

private theorem sixteenC8SpinIso_nonempty_fixRho_mulEquiv (K : Type) [Field K] [Finite K]
    [CharP K 2] : Nonempty (↥(fixRho K) ≃* ↥(StatedSp 3 K)) := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf, hK⟩ := FiniteField.card K 2
  have hf' : 1 ≤ (f : ℕ) := f.pos
  have hK' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hK
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  have hcomm := commutator_coordinateQuadPlus 4 K (by norm_num)
  have h : matrixDerivedScalars (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K)) = ⊥ := by
    apply CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo
    refine ⟨AutOm.vPlus one_le_four, ?_⟩
    change coordinateQuadPlus 4 K (AutOm.vPlus one_le_four) ≠ 0
    rw [AutOm.plusUnitVector_form one_le_four]
    exact one_ne_zero
  have hv : quadPlus 4 K (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) +
      Pi.single (Sum.inr (0 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) = 1 := by
    rw [quadPlus_apply]
    simp only [Pi.add_apply, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      simp at h
  have hvvec : reindexVectorEquiv (plusIndexEquiv 4)
      (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) + Pi.single (Sum.inr (0 : Fin 4)) (1 : K) :
        Fin 4 ⊕ Fin 4 → K) = AutOm.pvec (0 : Fin 4) true + AutOm.pvec (0 : Fin 4) false := by
    rw [map_add, AutOm.pvec_true, AutOm.pvec_false, AutOm.reindex_single, AutOm.reindex_single]
  let Q' := reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K)
  have hcast' : matrixDerived Q' = Om8 K := by
    unfold Om8 coordinateQuadPlus
    rfl
  let f' : matrixDerived Q' →* Om8 K :=
    { toFun := Eq.mp hcast'
      map_one' := by cases hcast'; rfl
      map_mul' := by intro a b; cases hcast'; rfl }
  let R : Subgroup (matrixDerived Q') := (fixRho K).comap f'
  have hmemR : ∀ z : matrixDerived Q', z ∈ R ↔ Eq.mp hcast' z ∈ fixRho K := fun z => Iff.rfl
  let e : StatedOmega (StatedQuadPlus 4 K) ≃* matrixDerived Q' :=
    statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
  let β : MulAut (StatedOmega (StatedQuadPlus 4 K)) :=
    omegaSymmetryAut (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) h
      (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) + Pi.single (Sum.inr (0 : Fin 4)) (1 : K) :
        Fin 4 ⊕ Fin 4 → K)
  have hfe : ∀ x : StatedOmega (StatedQuadPlus 4 K),
      Eq.mp hcast' (e x) = (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K)
        (coe_quadPlus 4 K) x : Om8 K) := by
    intro x
    cases hcast'
    rfl
  have key : ∀ x : StatedOmega (StatedQuadPlus 4 K), β x = x ↔ e x ∈ R := by
    intro x
    rw [hmemR, mem_fixRho_iff, hfe]
    have hβ : β x = x ↔ x ∈ fixedSubgroup β := Iff.rfl
    rw [hβ]
    dsimp only [β]
    have h2 := mem_fixedSubgroup_omegaSymmetryAut_iff (plusIndexEquiv 4) (quadPlus 4 K)
      (coe_quadPlus 4 K) h (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) +
        Pi.single (Sum.inr (0 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) hreg.1 hv x
    rw [h2, ← hvvec]
    have h3 := statedDerivedReindexEquiv_mulVec (plusIndexEquiv 4) (quadPlus 4 K)
      (coe_quadPlus 4 K) x (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) +
        Pi.single (Sum.inr (0 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K)
    rw [h3, (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).injective.eq_iff]
  have hfix : fixedSubgroup (MulAut.congr e β) = R := by
    ext y
    change (MulAut.congr e β) y = y ↔ y ∈ R
    have hc : (MulAut.congr e β) y = e (β (e.symm y)) := by
      rw [MulAut.congr_apply]
      rfl
    have h1 : e (β (e.symm y)) = y ↔ β (e.symm y) = e.symm y := by
      constructor
      · intro h
        apply e.injective
        rw [h, e.apply_symm_apply]
      · intro h
        rw [h, e.apply_symm_apply]
    rw [hc, h1, key, e.apply_symm_apply]
  have hmap : fixedSubgroup (MulAut.congr e β) = (fixedSubgroup β).map e.toMonoidHom := by
    ext y
    change (MulAut.congr e β) y = y ↔ y ∈ (fixedSubgroup β).map e.toMonoidHom
    rw [Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      have h1 : e (β (e.symm y)) = y := by
        have hc : (MulAut.congr e β) y = e (β (e.symm y)) := by
          rw [MulAut.congr_apply]
          rfl
        rw [hc] at hy
        exact hy
      have h2 : e (β (e.symm y)) = e (e.symm y) := by rw [h1, e.apply_symm_apply]
      exact e.injective h2
    · rintro ⟨x, hx, rfl⟩
      change e (β (e.symm (e x))) = e x
      rw [e.symm_apply_apply]
      exact congrArg e hx
  have hbij : Function.Bijective (f' : matrixDerived Q' → Om8 K) := by
    cases hcast'
    exact Function.bijective_id
  let ef : matrixDerived Q' ≃* Om8 K := MulEquiv.ofBijective f' hbij
  have hmapR : R.map ef.toMonoidHom = fixRho K := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hz
      refine ⟨ef.symm z, ?_, ef.apply_symm_apply z⟩
      change f' (ef.symm z) ∈ fixRho K
      rw [show f' (ef.symm z) = z from by
        change ef (ef.symm z) = z
        exact ef.apply_symm_apply z]
      exact hz
  obtain ⟨esp⟩ := nonempty_fixedSubgroup_omegaSymmetryAut_mulEquiv hf' hK' (by norm_num)
    (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) hreg.1 hreg.2 hcomm h hv
  let e1 : ↥(fixRho K) ≃* ↥R :=
    (MulEquiv.subgroupCongr hmapR).symm.trans
      (Subgroup.equivMapOfInjective R ef.toMonoidHom ef.injective).symm
  let e2 : ↥R ≃* ↥(fixedSubgroup (MulAut.congr e β)) :=
    (MulEquiv.subgroupCongr hfix).symm
  let e3 : ↥(fixedSubgroup (MulAut.congr e β)) ≃* ↥(fixedSubgroup β) :=
    (MulEquiv.subgroupCongr hmap).trans
      (Subgroup.equivMapOfInjective (fixedSubgroup β) e.toMonoidHom e.injective).symm
  exact ⟨(e1.trans e2).trans (e3.trans esp)⟩

theorem nonempty_spinSeven_mulEquiv (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nonempty (↥(spinSeven K) ≃* ↥(StatedSp 3 K)) := by
  obtain ⟨e⟩ := sixteenC8SpinIso_nonempty_fixRho_mulEquiv K
  refine ⟨((MulEquiv.subgroupCongr (spinSeven_eq (K := K))).trans
    (Subgroup.equivMapOfInjective (fixRho K) (theta : MulAut (Om8 K)).toMonoidHom
      (theta : MulAut (Om8 K)).injective).symm).trans e⟩

theorem isSpn_spinH : IsSpn ↥spinH 6 1 := by
  obtain ⟨e⟩ := nonempty_spinSeven_mulEquiv (ZMod 2)
  exact ⟨by decide, ZMod 2, inferInstance, inferInstance, by simp, ⟨spinHEquiv.symm.trans e⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
