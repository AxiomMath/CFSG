module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameDefs
public import CFSG.Blueprint.ChevalleyRootGroups
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.TwistedD4 (nd)


theorem rckTriD4Frame_D4
    {p₀ : ℕ} (S : LangSetup Tag.D4 GGL p₀) {h : ℕ} (hq : S.D.q = 2 ^ h)
    (hout : ¬ twistInner {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}
      (S.ρ : (Fin Tag.D4.rank → ℤ) → _)) :
    RCKTriD4Frame S {γ | IsRoot Tag.D4 γ} h := by
  classical
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hPne : P ≠ 1 := by
    rintro rfl
    have hΦ1 : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext g
      rw [hΦ g, one_mul, inv_one, mul_one]
    refine hout ⟨w, ?_, fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ1 hn hγ⟩
    have hsub : Set.range (simple Tag.D4) ⊆
        {s : WeylGroup Tag.D4 | ∃ γ ∈ {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ},
          s = rootReflection γ} := by
      rintro _ ⟨i, rfl⟩
      exact ⟨Pi.single i 1, isRoot_single Tag.D4 i, (rootReflection_single i).symm⟩
    have hmem : w ∈ Subgroup.closure (Set.range (simple Tag.D4)) := by
      rw [(coxeterSystem Tag.D4).subgroup_closure_range_simple]
      exact Subgroup.mem_top w
    exact Subgroup.closure_mono hsub hmem
  obtain ⟨t, ht, hPt⟩ := hP.resolve_left hPne
  let P0 : ModGL Tag.D4 GGL := diagramMap TwistTag.D4 GGL
  have hP' : P = P0 := by
    cases t with
    | E6 => exact absurd ht (by decide)
    | D4 =>
      subst hPt
      rw [show ht = rfl from Subsingleton.elim _ _]
      rfl
  have hFr' : Fr = iterateFrobenius GGL 2 h := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  have htw : S.D.Φ = (MulAut.conj P0).toMonoidHom.comp
      (Units.map (entrywiseHom (iterateFrobenius GGL 2 h))) := by
    refine MonoidHom.ext fun g => ?_
    rw [hΦ g, hP', hFr']
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have htriPsi : triPsi h 1 = (MulAut.conj P0).toMonoidHom.comp
      (Units.map (entrywiseHom (iterateFrobenius GGL 2 h))) := by
    rw [triPsi, pow_one]
    rfl
  have htri : S.D.Φ = triPsi h 1 := by
    rw [htriPsi, htw]
  have hspan : rootSpan Tag.D4 GGL {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}
      = adjointGroup Tag.D4 GGL :=
    (adjointGroup_eq_rootSpan (τ := Tag.D4) (K := GGL)).symm
  have hmaps : Set.MapsTo (S.ρ : (Fin Tag.D4.rank → ℤ) → _)
      {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}
      {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} :=
    fun γ hγ => (S.frob.isRoot_iff γ).2 hγ
  have hY : ∀ y ∈ rootSpan Tag.D4 GGL {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ},
      S.D.step y ∈ rootSpan Tag.D4 GGL {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} :=
    fun y hy => step_mem_rootSpan S (fun γ hγ => hγ) hmaps hy
  have hmap : (adjointGroup Tag.D4 GGL).map (MulAut.conj S.D.g0).toMonoidHom
      = adjointGroup Tag.D4 GGL :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer S.D.g0_mem)
  have hmapRoot : (rootSpan Tag.D4 GGL {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}).map
      (MulAut.conj S.D.g0).toMonoidHom = adjointGroup Tag.D4 GGL := by
    rw [hspan, hmap]
  let Ξ : ↥(rootSpan Tag.D4 GGL {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}) ≃*
      ↥(adjointGroup Tag.D4 GGL) :=
    ((rootSpan Tag.D4 GGL {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}).equivMapOfInjective
      (MulAut.conj S.D.g0).toMonoidHom (MulAut.conj S.D.g0).injective).trans
      (MulEquiv.subgroupCongr hmapRoot)
  have hΞ : ∀ (y : ModGL Tag.D4 GGL)
      (hy : y ∈ rootSpan Tag.D4 GGL {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}),
      (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) = S.D.g0 * y * S.D.g0⁻¹ := by
    intro y hy
    rfl
  have key : ∀ γ : Fin Tag.D4.rank → ℤ,
      (∀ y, y ∈ (rootSubgroup Tag.D4 GGL γ).map
          (MulAut.conj S.D.g0⁻¹).toMonoidHom ↔
        ∃ hy : y ∈ rootSpan Tag.D4 GGL {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ},
          (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈ rootSubgroup Tag.D4 GGL γ) := by
    intro γ y
    constructor
    · intro hy
      obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.1 hy
      have huAdj : u ∈ adjointGroup Tag.D4 GGL := rootSubgroup_le_adjointGroup γ hu
      have hyadj : y ∈ adjointGroup Tag.D4 GGL := by
        rw [← huy]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mul_mem (mul_mem (inv_mem S.D.g0_mem) huAdj) (inv_mem (inv_mem S.D.g0_mem))
      refine ⟨by rwa [hspan], ?_⟩
      have hconj : S.D.g0 * y * S.D.g0⁻¹ = u := by
        rw [← huy]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rw [hΞ, hconj]
      exact hu
    · rintro ⟨hy, hmem⟩
      refine Subgroup.mem_map.2 ⟨(Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL), hmem, ?_⟩
      rw [hΞ]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  refine ⟨1, Or.inl rfl, hY, Ξ, ?_, ?_⟩
  · intro y hy
    rw [hΞ, hΞ]
    calc S.D.g0 * S.D.step y * S.D.g0⁻¹
        = S.D.g0 * (S.D.n * S.D.Φ y * S.D.n⁻¹) * S.D.g0⁻¹ := by
          rw [LangDatum.step, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
            MulAut.conj_apply]
      _ = (S.D.g0 * S.D.n) * S.D.Φ y * (S.D.g0 * S.D.n)⁻¹ := by group
      _ = S.D.Φ S.D.g0 * S.D.Φ y * (S.D.Φ S.D.g0)⁻¹ := by rw [S.D.lang]
      _ = S.D.Φ (S.D.g0 * y * S.D.g0⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      _ = triPsi h 1 (S.D.g0 * y * S.D.g0⁻¹) := by rw [← htri]
  · refine ⟨S.D.g0⁻¹, hspan ▸ inv_mem S.D.g0_mem, Pi.single (nd 2) 1,
      isRoot_single Tag.D4 (nd 2), key (Pi.single (nd 2) 1), key (-Pi.single (nd 2) 1)⟩

end CFSG.StandardType.RCKRP

end
