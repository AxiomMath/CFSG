module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derSpIso
import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpDefs
import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestr
import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestrStd
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def l48sM_eiso {K : Type} [Field K] [Finite K] [CharP K 2] :
    LargeEvenProj (LargeEvenSpGroup K 4) ≃*
      ↥(TauCeti.BilinForm.isometryGroup (SmallRule.spBilin K 4)) :=
  ggB2der_spIso.trans (ggB2der_bridge (SmallRule.spBilin K 4))

private lemma l48sM_eiso_coe {K : Type} [Field K] [Finite K] [CharP K 2]
    (r : LargeEvenProj (LargeEvenSpGroup K 4)) :
    ((l48sM_eiso r : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
      Module.End K (Fin 4 ⊕ Fin 4 → K)) =
      (SmallRule.spRep r : Module.End K (Fin 4 ⊕ Fin 4 → K)) := by
  change ((ggB2der_bridge (SmallRule.spBilin K 4) (ggB2der_spIso r) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
      Module.End K (Fin 4 ⊕ Fin 4 → K)) = _
  rw [ggB2der_bridge_coe]
  exact ggB2der_spIso_coe r

private lemma l48sM_mem_iff {K : Type} [Field K] [Finite K] [CharP K 2]
    (W : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (s : LargeEvenProj (LargeEvenSpGroup K 4)) :
    s ∈ ggSpFixPerp W ↔
      (l48sM_eiso s : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
        A6Red.ggA6SpFixer (SmallRule.spBilin K 4)
          ((SmallRule.spBilin K 4).orthogonal W) := by
  constructor
  · intro hs
    refine ⟨(l48sM_eiso s).2, ?_⟩
    intro u hu
    exact (congrArg (fun f : Module.End K (Fin 4 ⊕ Fin 4 → K) => f u)
      (l48sM_eiso_coe s)).trans (hs u hu)
  · intro hs
    intro u hu
    exact (congrArg (fun f : Module.End K (Fin 4 ⊕ Fin 4 → K) => f u)
      (l48sM_eiso_coe s)).symm.trans (hs.2 u hu)

private noncomputable def l48sM_fixerEquiv {K : Type} [Field K] [Finite K] [CharP K 2]
    (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    ↥(ggSpFixPerp W) ≃*
      ↥(A6Red.ggA6SpFixer (SmallRule.spBilin K 4)
        ((SmallRule.spBilin K 4).orthogonal W)) := by
  set P : Submodule K (Fin 4 ⊕ Fin 4 → K) :=
    (SmallRule.spBilin K 4).orthogonal W with hPdef
  set SW : Subgroup (LargeEvenProj (LargeEvenSpGroup K 4)) := ggSpFixPerp W with hSWdef
  have hmem : ∀ s : LargeEvenProj (LargeEvenSpGroup K 4),
      s ∈ SW ↔ (l48sM_eiso s : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
        A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P := by
    intro s
    rw [hSWdef, hPdef]
    exact l48sM_mem_iff W s
  let res : ↥SW →* ↥(A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P) :=
    { toFun := fun s =>
        ⟨(l48sM_eiso s.1 : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)),
          (hmem s.1).mp s.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp }
  have hbij : Function.Bijective res := by
    constructor
    · intro a b h
      apply Subtype.ext
      have h1 : (res a).1 = (res b).1 :=
        congrArg (fun x : ↥(A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P) => x.1) h
      exact l48sM_eiso.injective (Subtype.ext h1)
    · intro g
      let r : LargeEvenProj (LargeEvenSpGroup K 4) := l48sM_eiso.symm ⟨g.1, g.2.1⟩
      have hr : l48sM_eiso r = ⟨g.1, g.2.1⟩ := l48sM_eiso.apply_symm_apply _
      have hrg : (l48sM_eiso r : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = g.1 :=
        congrArg (fun x : ↥(TauCeti.BilinForm.isometryGroup (SmallRule.spBilin K 4)) =>
          (x.1 : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) hr
      refine ⟨⟨r, ?_⟩, ?_⟩
      · rw [hmem r, hrg]
        exact g.2
      · apply Subtype.ext
        exact hrg
  exact MulEquiv.ofBijective res hbij

private noncomputable def l48sM_SW_perm {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hW : Module.finrank K W = 4)
    (hcompl : IsCompl W ((SmallRule.spBilin K 4).orthogonal W)) :
    ↥(ggSpFixPerp W) ≃* Equiv.Perm (Fin 6) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hB_alt : (SmallRule.spBilin K 4).IsAlt :=
    CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := 4) (K := K)
  have hB_nd : (SmallRule.spBilin K 4).Nondegenerate := SmallRule.spBilin_nondegenerate
  have hWnd : ((SmallRule.spBilin K 4).restrict W).Nondegenerate :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := SmallRule.spBilin K 4) hB_alt.isRefl).mpr hcompl
  have hdimW : Module.finrank K W = 2 * 2 := by rw [hW]
  let eRestr := Classical.choose
    (A6Red.ggA6_sp_restr_equiv (SmallRule.spBilin K 4) hB_alt hB_nd W hWnd)
  let eStd := Classical.choice (A6Red.ggA6_sp_std_equiv (V := Fin 4 ⊕ Fin 4 → K)
    ((SmallRule.spBilin K 4).restrict W) (fun x => hB_alt x) hWnd 2 hdimW)
  let ePerm := Classical.choice
    (CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := K) hKf)
  exact (l48sM_fixerEquiv W).trans (eRestr.trans (eStd.trans ePerm))

theorem ggB2der_small {G : Type} [Group G] [Finite G] {L J : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K 4)} (hψ : Function.Injective ψ)
    (hJL : J ≤ L) {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hW : Module.finrank K W = 4)
    (hcompl : IsCompl W ((SmallRule.spBilin K 4).orthogonal W))
    (hψJ : (J.subgroupOf L).map ψ = ⁅ggSpFixPerp W, ggSpFixPerp W⁆) :
    LargeEvenSmall J := by
  refine Or.inr ⟨?_⟩
  have eJ : ↥J ≃* ↥(J.subgroupOf L) := (Subgroup.subgroupOfEquivOfLe hJL).symm
  have eMap : ↥(J.subgroupOf L) ≃* ↥((J.subgroupOf L).map ψ) :=
    Subgroup.equivMapOfInjective (J.subgroupOf L) ψ hψ
  have eSWperm : ↥(ggSpFixPerp W) ≃* Equiv.Perm (Fin 6) := l48sM_SW_perm hK hW hcompl
  have e3 : Nonempty (↥⁅ggSpFixPerp W, ggSpFixPerp W⁆ ≃* alternatingGroup (Fin 6)) :=
    CFSG.RankThree.CASymplecticSubfield.nonempty_commutator_mulEquiv_alternating eSWperm
  exact eJ.trans (eMap.trans ((MulEquiv.subgroupCongr hψJ).trans e3.some))

end CFSG.StandardType

end
