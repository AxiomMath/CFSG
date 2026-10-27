module

public import CFSG.LocalAnalysis.StandardType.GGKGForkOmPlusRoot1
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2

private theorem ggKGOmR_center_bot {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hm : 4 ≤ m) :
    Subgroup.center (StatedOmega (StatedQuadPlus m K)) = ⊥ := by
  have hm3 : 3 ≤ m := by omega
  have : NeZero m := ⟨by omega⟩
  rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus hm3]
  refine TableBOrth.scalars_subgroupOf_omega_eq_bot (Q := StatedQuadPlus m K)
    (v₀ := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) (fun x v => ?_) ?_
  · rw [← CFSG.LieType.Universal.Spin.coe_quadPlus, QuadraticMap.map_smul, smul_eq_mul, sq]
  · rw [← CFSG.LieType.Universal.Spin.coe_quadPlus,
      CFSG.LieType.Universal.Spin.quadPlus_apply]
    simp [Pi.single_apply]

theorem ggKGOmR_isSimple {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 4 ≤ m) :
    IsSimpleGroup (StatedOmega (StatedQuadPlus m K)) := by
  have hm3 : 3 ≤ m := by omega
  have hZ := ggKGOmR_center_bot (K := K) (m := m) hm
  have hSc : (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf
      (StatedOmega (StatedQuadPlus m K)) = ⊥ := by
    rw [← CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus hm3]
    exact hZ
  let e : StatedProj (StatedOmega (StatedQuadPlus m K)) ≃*
      StatedOmega (StatedQuadPlus m K) :=
    (QuotientGroup.quotientMulEquivOfEq hSc).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup_congr.2
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus hm3)

theorem ggKGOmR_nonabelian {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 4 ≤ m) :
    ∃ a b : StatedOmega (StatedQuadPlus m K), a * b ≠ b * a := by
  classical
  by_contra h
  push Not at h
  haveI := ggKGOmR_isSimple (K := K) (m := m) hm
  have hZ := ggKGOmR_center_bot (K := K) (m := m) hm
  obtain ⟨a, b, hab⟩ := exists_pair_ne (StatedOmega (StatedQuadPlus m K))
  have ha : a = 1 := by
    have : a ∈ Subgroup.center (StatedOmega (StatedQuadPlus m K)) :=
      Subgroup.mem_center_iff.mpr fun c => h c a
    rw [hZ] at this
    simpa using this
  have hb : b = 1 := by
    have : b ∈ Subgroup.center (StatedOmega (StatedQuadPlus m K)) :=
      Subgroup.mem_center_iff.mpr fun c => h c b
    rw [hZ] at this
    simpa using this
  exact hab (ha.trans hb.symm)

theorem ggKGOmR_mem_orthDerived {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 4 ≤ m)
    (g : StatedOmega (StatedQuadPlus m K)) :
    toLinEquiv (Fin m ⊕ Fin m) K (g : GL (Fin m ⊕ Fin m) K) ∈
      CFSG.RankThree.Classical2.orthDerived (CFSG.LieType.Universal.Spin.quadPlus m K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hmap : (StatedOmega (StatedQuadPlus m K)).map
      (toLinEquiv (Fin m ⊕ Fin m) K).toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (CFSG.LieType.Universal.Spin.quadPlus m K) := by
    rw [statedOmega_eq_comap (CFSG.LieType.Universal.Spin.coe_quadPlus m K)]
    exact Subgroup.map_comap_eq_self_of_surjective
      (toLinEquiv (Fin m ⊕ Fin m) K).surjective _
  exact hmap ▸ Subgroup.mem_map_of_mem _ g.2

theorem ggKGOmR_isChevSimple {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 4 ≤ m) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      (StatedOmega (StatedQuadPlus m K)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hring : ringChar K = 2 := ringChar.eq (R := K) 2
  let Q := CFSG.LieType.Universal.Spin.quadPlus m K
  have hQ : Q.polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K
  have hmap : (StatedOmega (StatedQuadPlus m K)).map
      (toLinEquiv (Fin m ⊕ Fin m) K).toMonoidHom = orthDerived Q := by
    rw [statedOmega_eq_comap (CFSG.LieType.Universal.Spin.coe_quadPlus m K)]
    exact Subgroup.map_comap_eq_self_of_surjective
      (toLinEquiv (Fin m ⊕ Fin m) K).surjective _
  let e : StatedOmega (StatedQuadPlus m K) ≃* orthDerived Q :=
    ((toLinEquiv (Fin m ⊕ Fin m) K).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  have hqG : CFSG.IsQuasisimple (StatedOmega (StatedQuadPlus m K)) :=
    CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus (K := K) (by omega)
  haveI hSimpL : IsSimpleGroup (orthDerived Q) :=
    e.symm.isSimpleGroup_congr.2 (ggKGOmR_isSimple (K := K) (m := m) hm)
  have hncL : ∃ a b : orthDerived Q, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := ggKGOmR_nonabelian (K := K) (m := m) hm
    exact ⟨e a, e b, fun hc => hab (e.injective (by simpa using hc))⟩
  have hZ_L : Subgroup.center (orthDerived Q) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hncL
  have hZtop : Subgroup.center (↥(⊤ : Subgroup (orthDerived Q))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (Subgroup.topEquiv x : orthDerived Q) ∈ Subgroup.center (orthDerived Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := Subgroup.topEquiv.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
    rw [hZ_L, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa using hx')
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorFacts_holds
      K (Fin m ⊕ Fin m → K) Q hQ (⊤ : Subgroup (orthDerived Q)) inferInstance
      (hqG.of_mulEquiv e.symm |>.of_mulEquiv Subgroup.topEquiv)
  have hX2 : LieFactorData 2 X := by rwa [hring] at hX
  obtain ⟨e1⟩ := nonempty_centralQuotient_mulEquiv hX2.perfect f hf hfk
  let e2 : X ⧸ Subgroup.center X ≃* StatedOmega (StatedQuadPlus m K) :=
    e1.trans ((QuotientGroup.quotientMulEquivOfEq hZtop).trans
      QuotientGroup.quotientBot |>.trans (Subgroup.topEquiv.trans e.symm))
  exact isChevSimple_congr e2 hX2.chev

end CFSG.StandardType

end
