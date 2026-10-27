module

public import CFSG.LieType.Steinberg.Minuscule.RootCentralizer
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SplitTorus
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LieType.AlgebraicGroups.RootSL2Centralizer
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerConnectedComponent
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.RankThree.Classical2.SLnFrobeniusFormFixed
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import CFSG.HardMathSupport.Lang.AnisoE6.ConjRoot
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.MultiModelGlue
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd
public import CFSG.HardMathSupport.Foote.Proving.RootStringOne
public import CFSG.HardMathSupport.Lang.AnisoE8.D8Planes
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveOrbit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.AlgebraicGroups
  CFSG.LieType.CurtisTits CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T

theorem e7_commute_pinnedX_baseChange_of_commute_xm_one
    {k Ω : Type} [Field k] [Finite k] [CharP k 2] [Field Ω] [CharP Ω 2]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    {y : e7Data_valid.minGroup k} {gamma : Fin (Tag.rank .E7) → ℤ}
    (hgamma : IsRoot .E7 gamma) (h : Commute y (e7Data_valid.xm k gamma 1)) (c : Ω) :
    Commute (baseChangeGL (algebraMap k Ω)
      ((e7Isogeny k y : adjointGroup .E7 k) : ModGL .E7 k)) (pinnedX .E7 Ω gamma c) := by
  let E : IntermediateField k Ω := IntermediateField.adjoin k ({c} : Set Ω)
  letI : FiniteDimensional k E :=
    IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic c).isIntegral)
  letI : Finite E := Module.finite_of_finite k
  let ce : E := ⟨c, IntermediateField.mem_adjoin_simple_self k c⟩
  have hc : Commute (minBC e7Data_valid (algebraMap k E) y)
      (e7Data_valid.xm E gamma ce) :=
    commute_xm_baseChange_of_commute_xm_one e7Data_valid (algebraMap k E) h ce
  have ha := (hc.map (e7Isogeny E)).map (adjointGroup .E7 E).subtype
  change Commute ((e7Isogeny E (minBC e7Data_valid (algebraMap k E) y) :
    adjointGroup .E7 E) : ModGL .E7 E)
    ((e7Isogeny E (e7Data_valid.xm E gamma ce) : adjointGroup .E7 E) : ModGL .E7 E) at ha
  rw [CFSG.LieType.SeitzGeneration.ExcHigh.E7S.isogeny_minBC,
    CFSG.SeitzReduction.E8Pilot.coe_e7Isogeny_xm hgamma] at ha
  let inc : E →+* Ω := E.toSubfield.subtype
  have hinc : inc.comp (algebraMap k E) = algebraMap k Ω := by
    ext a
    rfl
  have hce : inc ce = c := by
    rfl
  have hz := congrArg (baseChangeGL inc) ha.eq
  change _ * _ = _ * _
  simpa only [map_mul, baseChangeGL_baseChangeGL, baseChangeGL_pinnedX, hinc, hce] using hz

theorem e7_rootSL2_mem_connectedCentralizer_of_component
    {k Ω : Type} [Field k] [Finite k] [CharP k 2] [Field Ω] [CharP Ω 2]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (i : Fin (Tag.rank .E7)) {y : e7Data_valid.minGroup k}
    {M : Subgroup (e7Data_valid.minGroup k)}
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({y} : Set (e7Data_valid.minGroup k))))
    (hR : rankOne (e7Datum k).rootGroup i ≤ M) (A : SL2 Ω) :
    rootSL2 .E7 Ω (Pi.single i 1) A ∈ closedIdentityComponent
      (adjointGroup .E7 Ω ⊓ Subgroup.centralizer
        (Set.singleton (baseChangeGL (algebraMap k Ω)
          ((e7Isogeny k y : adjointGroup .E7 k) : ModGL .E7 k)))) := by
  let gamma : Fin (Tag.rank .E7) → ℤ := Pi.single i 1
  have hC := hR.trans hM.1
  change e7Data_valid.rootGroup k gamma ⊔ e7Data_valid.rootGroup k (-gamma) ≤ _ at hC
  have hp : Commute y (e7Data_valid.xm k gamma 1) :=
    Subgroup.mem_centralizer_iff.mp
      ((le_sup_left.trans hC) (e7Data_valid.xm_mem_rootGroup k gamma 1)) y rfl
  have hn : Commute y (e7Data_valid.xm k (-gamma) 1) :=
    Subgroup.mem_centralizer_iff.mp
      ((le_sup_right.trans hC) (e7Data_valid.xm_mem_rootGroup k (-gamma) 1)) y rfl
  apply rootSL2_mem_closedIdentityComponent_of_commute (isRoot_single .E7 i)
  intro z hz B
  obtain rfl : z = baseChangeGL (algebraMap k Ω)
      ((e7Isogeny k y : adjointGroup .E7 k) : ModGL .E7 k) := hz
  apply (CFSG.HardMathSupport.Lang.AnisoE6.commute_of_forall_pinnedX Ω ?_
    (rootSL2_mem_rootSpan_pair (isRoot_single .E7 i) B)).eq
  intro delta hdelta c
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdelta
  rcases hdelta with rfl | rfl
  · exact e7_commute_pinnedX_baseChange_of_commute_xm_one (isRoot_single .E7 i) hp c
  · exact e7_commute_pinnedX_baseChange_of_commute_xm_one (isRoot_neg_single .E7 i) hn c

open CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T

theorem e7_rootSL2_conj_mem_connectedCentralizer_of_component
    {k Ω : Type} [Field k] [Finite k] [CharP k 2] [Field Ω] [CharP Ω 2]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (i : Fin (Tag.rank .E7)) {y : e7Data_valid.minGroup k}
    {M : Subgroup (e7Data_valid.minGroup k)}
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({y} : Set (e7Data_valid.minGroup k))))
    (hR : rankOne (e7Datum k).rootGroup i ≤ M)
    (S : LangSetup .E7 Ω 5) (iota : adjointGroup .E7 k →* ModGL .E7 Ω)
    (hiota : ∀ c, iota c = S.D.g0⁻¹ * baseChangeGL (algebraMap k Ω)
      (c : ModGL .E7 k) * S.D.g0)
    (a : Fin (Tag.rank .E7) → Ωˣ)
    (hy : iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint k y) = rootDiagUnit .E7 a)
    (A : SL2 Ω) :
    S.D.g0⁻¹ * rootSL2 .E7 Ω (Pi.single i 1) A * S.D.g0 ∈
      closedIdentityComponent (adjointGroup .E7 Ω ⊓
        Subgroup.centralizer ({rootDiagUnit .E7 a} : Set (ModGL .E7 Ω))) := by
  let yBC : ModGL .E7 Ω := baseChangeGL (algebraMap k Ω)
    ((e7Isogeny k y : adjointGroup .E7 k) : ModGL .E7 k)
  let C : Subgroup (ModGL .E7 Ω) := adjointGroup .E7 Ω ⊓
    Subgroup.centralizer ({yBC} : Set (ModGL .E7 Ω))
  let phi : ModGL .E7 Ω →* ModGL .E7 Ω := (MulAut.conj S.D.g0⁻¹).toMonoidHom
  have hactor : phi yBC = rootDiagUnit .E7 a := by
    change S.D.g0⁻¹ * yBC * S.D.g0 = _
    simpa only [yBC, CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint_apply] using
      (hiota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint k y)).symm.trans hy
  have hCmap : C.map phi ≤ adjointGroup .E7 Ω ⊓
      Subgroup.centralizer ({rootDiagUnit .E7 a} : Set (ModGL .E7 Ω)) := by
    rintro z ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · change S.D.g0⁻¹ * w * S.D.g0 ∈ adjointGroup .E7 Ω
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ S.D.g0_mem) hw.1) S.D.g0_mem
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hc : w * yBC = yBC * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
      simpa only [map_mul, hactor] using congrArg phi hc
  have hA : rootSL2 .E7 Ω (Pi.single i 1) A ∈ closedIdentityComponent C :=
    e7_rootSL2_mem_connectedCentralizer_of_component i hM hR A
  have hAC : phi (rootSL2 .E7 Ω (Pi.single i 1) A) ∈
      closedIdentityComponent (C.map phi) :=
    closedIdentityComponent_map_conj_le C S.D.g0⁻¹ (Subgroup.mem_map_of_mem phi hA)
  change phi (rootSL2 .E7 Ω (Pi.single i 1) A) ∈ _
  exact closedIdentityComponent_mono hCmap hAC

theorem e7_rootSL2_conj_mem_kernelRootSpan_of_component
    {k Ω : Type} [Field k] [Finite k] [CharP k 2] [Field Ω] [CharP Ω 2]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (i : Fin (Tag.rank .E7)) {y : e7Data_valid.minGroup k}
    {M : Subgroup (e7Data_valid.minGroup k)}
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({y} : Set (e7Data_valid.minGroup k))))
    (hR : rankOne (e7Datum k).rootGroup i ≤ M)
    (S : LangSetup .E7 Ω 5) (iota : adjointGroup .E7 k →* ModGL .E7 Ω)
    (hiota : ∀ c, iota c = S.D.g0⁻¹ * baseChangeGL (algebraMap k Ω)
      (c : ModGL .E7 k) * S.D.g0)
    (a : Fin (Tag.rank .E7) → Ωˣ)
    (hy : iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint k y) = rootDiagUnit .E7 a)
    (A : SL2 Ω) :
    S.D.g0⁻¹ * rootSL2 .E7 Ω (Pi.single i 1) A * S.D.g0 ∈
      rootSpan .E7 Ω (rootCharKernel a) := by
  letI : Group.IsPerfect (SL2 Ω) :=
    CFSG.RankThree.Classical2.isPerfect_specialLinearGroup_of_infinite (by decide)
  let phi : SL2 Ω →* ModGL .E7 Ω :=
    (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp (rootSL2 .E7 Ω (Pi.single i 1))
  have hC : phi.range ≤ closedIdentityComponent (toralCentralizer .E7 Ω a) := by
    rintro z ⟨B, rfl⟩
    exact CFSG.StandardType.e7_rootSL2_conj_mem_connectedCentralizer_of_component
      i hM hR S iota hiota a hy B
  change phi A ∈ _
  exact range_le_rootSpan_of_perfect_of_le_connectedCentralizer a phi hC ⟨A, rfl⟩

theorem e7_rootSL2_conj_mem_e6ComponentRootSpan_of_component
    {k Ω : Type} [Field k] [Finite k] [CharP k 2] [Field Ω] [CharP Ω 2]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (i : Fin (Tag.rank .E7)) {y : e7Data_valid.minGroup k}
    {M : Subgroup (e7Data_valid.minGroup k)}
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({y} : Set (e7Data_valid.minGroup k))))
    (hR : rankOne (e7Datum k).rootGroup i ≤ M)
    (S : LangSetup .E7 Ω 5) (iota : adjointGroup .E7 k →* ModGL .E7 Ω)
    (hiota : ∀ c, iota c = S.D.g0⁻¹ * baseChangeGL (algebraMap k Ω)
      (c : ModGL .E7 k) * S.D.g0)
    (a : Fin (Tag.rank .E7) → Ωˣ)
    (hy : iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint k y) = rootDiagUnit .E7 a)
    (c : KernelComponent (rootCharHom a)) (v : WeylGroup .E7)
    (hPsi : componentRoots (rootCharHom a) c =
      (fun alpha => v • alpha) '' parabolicRoots .E7 (e6Nodes .E7)) (A : SL2 Ω) :
    S.D.g0⁻¹ * rootSL2 .E7 Ω (Pi.single i 1) A * S.D.g0 ∈
      rootSpan .E7 Ω (componentRoots (rootCharHom a) c) := by
  have hk := CFSG.HardMathSupport.Timmesfeld.LangTorus.kernelRoots_eq_componentRoots_of_E7_e6 (rootCharHom a) c v hPsi
  rw [kernelRoots_rootCharHom] at hk
  rw [← hk]
  exact e7_rootSL2_conj_mem_kernelRootSpan_of_component i hM hR S iota hiota a hy A

end CFSG.StandardType
