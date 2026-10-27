module

public import CFSG.ClassicalGroups.Orthogonal.FiveSquareSylow
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21a
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21c
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticCommutant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryComponents
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.Existence.Monolith
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Orthogonal

theorem isConj_zD_of_dvd_card_centralizer {t : FiveSquareFrameGeneration.derived}
    (ht : orderOf t = 2)
    (h64 : 64 ∣ Nat.card (Subgroup.centralizer ({t} : Set FiveSquareFrameGeneration.derived))) :
    IsConj FiveSquareFrameGeneration.zD t := by
  classical
  have hcardΩ : Nat.card FiveSquareFrameGeneration.derived = 4680000 :=
    FiveSquareSylow.card_G
  haveI : Finite FiveSquareFrameGeneration.derived :=
    Nat.finite_of_card_ne_zero (by rw [hcardΩ]; norm_num)
  let C : Subgroup FiveSquareFrameGeneration.derived :=
    Subgroup.centralizer ({t} : Set FiveSquareFrameGeneration.derived)
  have h64C : 64 ∣ Nat.card C := h64
  have hdvd : 2 ^ 6 ∣ Nat.card C := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
    exact h64C
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 (n := 6) hdvd
  let P : Subgroup FiveSquareFrameGeneration.derived := K.map C.subtype
  have hPcard : Nat.card P = 2 ^ 6 := by
    change Nat.card ↥(K.map C.subtype) = 2 ^ 6
    rw [Subgroup.card_map_of_injective C.subtype_injective, hKcard]
  have hPgroup : IsPGroup 2 P := IsPGroup.of_card hPcard
  have hindex : P.index = 73125 := by
    have h := Subgroup.index_mul_card (G := FiveSquareFrameGeneration.derived) (H := P)
    rw [hPcard, hcardΩ] at h
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h
    have h' : P.index * 64 = 73125 * 64 := by rw [h]
    exact Nat.eq_of_mul_eq_mul_right (m := 64) (by norm_num) h'
  have hnotdvd : ¬ 2 ∣ P.index := by rw [hindex]; norm_num
  let P_sylow : Sylow 2 FiveSquareFrameGeneration.derived := hPgroup.toSylow hnotdvd
  have hP_sylow_coe : (P_sylow : Subgroup FiveSquareFrameGeneration.derived) = P :=
    IsPGroup.toSylow_coe hPgroup hnotdvd
  have hPC : P ≤ C := Subgroup.map_subtype_le K
  have hZ : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  have hcent_eq : Subgroup.centralizer ({t} : Set FiveSquareFrameGeneration.derived) =
      Subgroup.centralizer (Subgroup.zpowers t : Set FiveSquareFrameGeneration.derived) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hHK : P ≤ Subgroup.normalizer (Subgroup.zpowers t) := by
    have h1 : P ≤ Subgroup.centralizer
        (Subgroup.zpowers t : Set FiveSquareFrameGeneration.derived) := by
      rw [← hcent_eq]
      exact hPC
    exact h1.trans (Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers t : Set FiveSquareFrameGeneration.derived))
  have hsup : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers t) :=
    IsPGroup.to_sup_of_normal_right' hPgroup hZ hHK
  have hmax : P ⊔ Subgroup.zpowers t = P := P_sylow.is_maximal' hsup le_sup_left
  have htP : t ∈ P := by
    have ht_sup : t ∈ P ⊔ Subgroup.zpowers t :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rwa [hmax] at ht_sup
  have ht_center : (⟨t, htP⟩ : P) ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hPC y.2))
  haveI : Finite (Sylow 2 FiveSquareFrameGeneration.derived) :=
    Sylow.finite_of_finiteIndex P_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq FiveSquareFrameGeneration.derived P_sylow
    FiveSquareSylow.frameSylowClass
  have hgP : ((g • P_sylow : Sylow 2 FiveSquareFrameGeneration.derived) :
      Subgroup FiveSquareFrameGeneration.derived) = FiveSquareSylow.frameSylow :=
    (congrArg (fun S : Sylow 2 FiveSquareFrameGeneration.derived =>
      (S : Subgroup FiveSquareFrameGeneration.derived)) hg).trans
      FiveSquareSylow.coe_frameSylowClass
  have hmem : ∀ y : FiveSquareFrameGeneration.derived,
      y ∈ FiveSquareSylow.frameSylow ↔ g⁻¹ * y * g ∈ P := by
    intro y
    rw [← hgP, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      hP_sylow_coe, ← map_inv MulAut.conj g, MulAut.smul_def, MulAut.conj_apply]
    simp
  have hconj_mem : g * t * g⁻¹ ∈ FiveSquareSylow.frameSylow :=
    (hmem (g * t * g⁻¹)).mpr (by
      have heq : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [heq]
      exact htP)
  have hcenter : (⟨g * t * g⁻¹, hconj_mem⟩ : FiveSquareSylow.frameSylow) ∈
      Subgroup.center FiveSquareSylow.frameSylow := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨p, hp, hp_eq⟩ :
        ∃ p ∈ P, g * p * g⁻¹ = (y : FiveSquareFrameGeneration.derived) :=
      ⟨g⁻¹ * (y : FiveSquareFrameGeneration.derived) * g, (hmem (y : _)).mp y.2, by group⟩
    apply Subtype.ext
    have hpt : p * t = t * p := by
      have hc := Subgroup.mem_center_iff.mp ht_center (⟨p, hp⟩ : P)
      simpa using congrArg Subtype.val hc
    change (y : FiveSquareFrameGeneration.derived) * (g * t * g⁻¹)
      = (g * t * g⁻¹) * (y : FiveSquareFrameGeneration.derived)
    rw [← hp_eq]
    calc (g * p * g⁻¹) * (g * t * g⁻¹)
        = g * (p * t) * g⁻¹ := by group
      _ = g * (t * p) * g⁻¹ := by rw [hpt]
      _ = (g * t * g⁻¹) * (g * p * g⁻¹) := by group
  have hmem_zpowers : g * t * g⁻¹ ∈ Subgroup.zpowers FiveSquareFrameGeneration.zD := by
    rw [← FiveSquareSylow.center_frameSylow_map]
    exact Subgroup.mem_map.mpr ⟨⟨g * t * g⁻¹, hconj_mem⟩, hcenter, rfl⟩
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two FiveSquareSylow.orderOf_zD).mp
      hmem_zpowers with h1 | hz
  · exfalso
    have hord : orderOf (g * t * g⁻¹) = 2 := by
      have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t
      rw [ht] at h
      rw [← MulAut.conj_apply g t]
      simpa only [MulEquiv.coe_toMonoidHom] using h
    rw [h1, orderOf_one] at hord
    omega
  · exact isConj_comm.mpr (isConj_iff.mpr ⟨g, hz⟩)

end CFSG.OddTranspositions.PartThree
