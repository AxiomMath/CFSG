module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOn
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOrth
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharSp
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin GGOrthRad
open scoped Pointwise

section Abstract

variable {P : Type*} [Group P]

private theorem isCharacteristicP_of_comap_conj {p : ℕ} {M : Subgroup P} (y : P)
    (h : IsCharacteristicP p ↥(M.comap (MulAut.conj y).toMonoidHom)) : IsCharacteristicP p ↥M := by
  have hc : M.comap (MulAut.conj y).toMonoidHom = M.map (MulAut.conj y).symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm (MulAut.conj y) M
  exact CFSG.RankThree.PartTwo.Sec14.isCharacteristicP_of_mulEquiv'
    ((MulEquiv.subgroupCongr hc).trans (Subgroup.equivMapOfInjective M
      (MulAut.conj y).symm.toMonoidHom (MulAut.conj y).symm.injective).symm) h

theorem ggNormalizerOvergroupsChar_of_borel [Finite P] (p : ℕ) [Fact p.Prime] (B : Subgroup P)
    (U : Sylow p P) (hU : B = normalizer ((U : Subgroup P) : Set P))
    (hB : ∀ M : Subgroup P, IsCoatom M → B ≤ M → IsCharacteristicP p ↥M) :
    GGNormalizerOvergroupsChar p P := by
  refine GGNormalizerOvergroupsChar.of_coatoms fun S M hS hSi hNM hM => ?_
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq P U (hS.toSylow hSi)
  have hSy : (U : Subgroup P).map (MulAut.conj y).toMonoidHom = S := by
    have h1 := congrArg (fun T : Sylow p P => (T : Subgroup P)) hy
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [Subgroup.pointwise_smul_def] at h1
    exact h1
  have hBM : B ≤ M.comap (MulAut.conj y).toMonoidHom := by
    rw [← Subgroup.map_le_iff_le_comap, hU, Subgroup.map_equiv_normalizer_eq, hSy]
    exact hNM
  exact isCharacteristicP_of_comap_conj y
    (hB _ ((Subgroup.isCoatom_comap (MulAut.conj y)).2 hM) hBM)

end Abstract

section Stated

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private noncomputable def projEquivMk (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    StatedProj (StatedOmega Q0) ≃* ProjElementary Q :=
  QuotientGroup.congr _ _ (statedOmegaEquiv hQ hE) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hy
      rw [Subgroup.mem_subgroupOf]
      change ((statedOmegaEquiv hQ hE y : elementaryGroup Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈
        scalars K (ι → K)
      rw [coe_statedOmegaEquiv]
      exact hy
    · intro hx
      refine ⟨(statedOmegaEquiv hQ hE).symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
      rw [Subgroup.mem_subgroupOf] at hx
      have h1 : (statedOmegaEquiv hQ hE ((statedOmegaEquiv hQ hE).symm x) :
          (ι → K) ≃ₗ[K] (ι → K)) = x := by rw [MulEquiv.apply_symm_apply]
      rw [coe_statedOmegaEquiv] at h1
      rw [h1]
      exact hx)

theorem isCharacteristicP_statedProjectiveSubspaceStabilizer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p ≠ 2) (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hQn : Q.polarBilin.Nondegenerate) (hV : 5 ≤ Module.finrank K (ι → K))
    {W : Submodule K (ι → K)} (h0 : W ≠ ⊥) (hW : ∀ w ∈ W, Q0 w = 0) :
    IsCharacteristicP p ↥(statedProjectiveSubspaceStabilizer Q0 W) := by
  have hchar := isCharacteristicP_orthProjStabilizer p hp Q hQn hV h0 fun w hw => hQ ▸ hW w hw
  have hD : (statedDerivedSubspaceStabilizer Q0 W).map (statedOmegaEquiv hQ hE).toMonoidHom =
      stabE Q W := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hx
      refine ⟨(statedOmegaEquiv hQ hE).symm x, ?_, by simp⟩
      change W.map ((toLinEquiv ι K (((statedOmegaEquiv hQ hE).symm x : StatedOmega Q0) :
        GL ι K)).toLinearMap) = W
      have h1 : toLinEquiv ι K (((statedOmegaEquiv hQ hE).symm x : StatedOmega Q0) : GL ι K) =
          (x : (ι → K) ≃ₗ[K] (ι → K)) := by
        rw [← coe_statedOmegaEquiv hQ hE, MulEquiv.apply_symm_apply]
      rw [h1]
      exact hx
  have hmap : (statedProjectiveSubspaceStabilizer Q0 W).map (projEquivMk Q hQ hE).toMonoidHom =
      (stabE Q W).map (QuotientGroup.mk' ((scalars K (ι → K)).subgroupOf (elementaryGroup Q))) := by
    rw [← statedDerivedSubspaceStabilizer_map, Subgroup.map_map, ← hD, Subgroup.map_map]
    congr 1
  exact CFSG.RankThree.PartTwo.Sec14.isCharacteristicP_of_mulEquiv'
    ((MulEquiv.subgroupCongr hmap.symm).trans (Subgroup.equivMapOfInjective _
      (projEquivMk Q hQ hE).toMonoidHom (projEquivMk Q hQ hE).injective).symm) hchar

theorem ggNormalizerOvergroupsChar_statedProj_of_borelInterface [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : p ≠ 2) (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hQn : Q.polarBilin.Nondegenerate) (hV : 5 ≤ Module.finrank K (ι → K)) {r : ℕ}
    {F : Fin r → Submodule K (ι → K)} (hI : BorelInterface p Q0 F) :
    GGNormalizerOvergroupsChar p (StatedProj (StatedOmega Q0)) := by
  haveI : Finite (GL ι K) :=
    Finite.of_injective (fun g : GL ι K => (g : Matrix ι ι K)) Units.val_injective
  haveI : Finite (StatedProj (StatedOmega Q0)) := inferInstance
  obtain ⟨hF, ⟨U, hU⟩, -, hcoatom, -⟩ := hI
  refine ggNormalizerOvergroupsChar_of_borel p _ U hU fun M hM hBM => ?_
  obtain ⟨i, rfl⟩ := hcoatom M hM hBM
  refine isCharacteristicP_statedProjectiveSubspaceStabilizer p hp Q hQ hE hQn hV ?_ (hF i).1
  intro h
  have := (hF i).2
  rw [h, finrank_bot] at this
  omega

end Stated

variable {r : ℕ}

theorem ggLieParabolicCharInputOn_B :
    GGLieParabolicCharInputOn fun d => ∃ r q, d.1 = .B r q := by
  rintro K _ _ d ⟨r, q, hm⟩ ⟨e⟩ hp2 S X hS hSi hNX hX
  have hp : d.1.characteristic = q.p := by
    rw [hm]
    exact TauCeti.LieTypeIndex.characteristic_B r q
  rw [hp] at hp2 hS hSi ⊢
  have hv : (TauCeti.LieTypeIndex.B r q).Valid := hm ▸ d.2
  obtain rfl : d = ⟨.B r q, hv⟩ := Subtype.ext hm
  have hr : 2 ≤ r :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · obtain ⟨-, K', _, _, hcard, ⟨φ⟩⟩ := QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    haveI := Fintype.ofFinite K'
    haveI : CharP K' q.p := charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card, hcard])
    exact (GGNormalizerOvergroupsChar.of_mulEquiv φ
      (ggNormalizerOvergroupsChar_statedProjSp q.p (by omega))) S X hS hSi hNX hX
  · have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr3 e
    have hI := orthogonal_geometry_tail_model_Borel_overgroup_interface K .POmegaOdd (Or.inl rfl)
      r q.p q.exponent hmodel
    obtain ⟨-, K', _, _, hcard, ⟨φ⟩⟩ := hmodel
    haveI := Fintype.ofFinite K'
    haveI : CharP K' q.p := charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card, hcard])
    have h2 : (2 : K') ≠ 0 := two_ne_zero_of_charP q.p hp2
    exact (GGNormalizerOvergroupsChar.of_mulEquiv φ
      (ggNormalizerOvergroupsChar_statedProj_of_borelInterface q.p hp2 (quadOdd r K')
        (coe_quadOdd r K') (commutator_orthogonalGroup_quadOdd h2 hr3)
        (nondegenerate_polarBilin_quadOdd r K' h2)
        (by rw [Module.finrank_fintype_fun_eq_card]; simp; omega)
        (hI K' hcard))) S X hS hSi hNX hX

theorem ggLieParabolicCharInputOn_twistedD :
    GGLieParabolicCharInputOn fun d => ∃ r q, d.1 = .twistedD r q := by
  rintro K _ _ d ⟨r, q, hm⟩ ⟨e⟩ hp2 S X hS hSi hNX hX
  have hp : d.1.characteristic = q.p := by
    rw [hm]
    exact TauCeti.LieTypeIndex.characteristic_twistedD r q
  rw [hp] at hp2 hS hSi ⊢
  have hv : (TauCeti.LieTypeIndex.twistedD r q).Valid := hm ▸ d.2
  obtain rfl : d = ⟨.twistedD r q, hv⟩ := Subtype.ext hm
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  have hI := orthogonal_geometry_tail_model_Borel_overgroup_interface K .POmegaMinus (Or.inr rfl)
    r q.p q.exponent hmodel
  obtain ⟨hadm, K', _, _, hcard, b, c, hirr, ⟨φ⟩⟩ := hmodel
  haveI := Fintype.ofFinite K'
  haveI : CharP K' q.p := charP_of_card_eq_prime_pow (f := q.exponent)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  have hr4 : 4 ≤ r := hadm.2.2
  exact (GGNormalizerOvergroupsChar.of_mulEquiv φ
    (ggNormalizerOvergroupsChar_statedProj_of_borelInterface q.p hp2 (quadMinus r K' b c)
      (coe_quadMinus r K' b c) (commutator_orthogonalGroup_quadMinus hr4 hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite r K' hirr)
      (by rw [Module.finrank_fintype_fun_eq_card]; simp; omega)
      (hI K' hcard b c hirr))) S X hS hSi hNX hX

end CFSG.StandardType
