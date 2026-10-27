module

public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.LieType.Universal.Catalog
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar

section Diagonal


theorem twInndiagGroup_le_twistedE6InndiagGL {K : Type} [Field K] (σ : K ≃+* K) :
    RecipeExcLang.twInndiagGroup K σ ≤ twistedE6InndiagGL K σ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro w (hw | ⟨b, hb, rfl⟩)
  · exact Subgroup.mem_sup_left hw
  · obtain ⟨u, hu⟩ := CFSG.LieType.Chevalley.exists_compatDiag_eq (t := TwistTag.E6)
      (σ := σ.toRingHom) hb
    have hmem : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
        twistedE6DiagGL K σ := ⟨u, rfl⟩
    rw [hu] at hmem
    exact Subgroup.mem_sup_right hmem

end Diagonal

section Ambient


@[expose] noncomputable def twInndiagToRgrp {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    ↥(RecipeExcLang.twInndiagGroup K σ) →* ↥(TwistedDiag.Rgrp L Fr) where
  toFun w := ⟨baseChangeGL (algebraMap K L) (w : ModGL TwistTag.E6.tag K),
    RecipeExcLang.baseChangeGL_mem_twistedFixed_of_mem_twInndiag hn hK hσ (L := L) (Fr := Fr)
      hFr w.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' := fun w v => Subtype.ext (map_mul _ _ _)

@[expose] noncomputable def twInndiagEquivRgrp {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    ↥(RecipeExcLang.twInndiagGroup K σ) ≃* ↥(TwistedDiag.Rgrp L Fr) :=
  MulEquiv.ofBijective (twInndiagToRgrp hn hK σ hσ Fr hFr)
    ⟨fun a b hab => by
        have hab' : (twInndiagToRgrp hn hK σ hσ Fr hFr a : ModGL Tag.E6 L) =
            (twInndiagToRgrp hn hK σ hσ Fr hFr b : ModGL Tag.E6 L) :=
          congrArg Subtype.val hab
        change baseChangeGL (algebraMap K L) (a : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap K L) (b : ModGL TwistTag.E6.tag K) at hab'
        exact Subtype.ext (baseChangeGL_injective (algebraMap K L) hab'),
      fun x => by
        obtain ⟨hxG, hxF⟩ := (TwistedDiag.mem_Rgrp Fr).1 x.2
        obtain ⟨w, hw, hwx⟩ := RecipeExcLang.exists_mem_twInndiag_of_twist_fixed hn hK hσ
          (L := L) (Fr := Fr) hFr hxG hxF
        refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
        change baseChangeGL (algebraMap K L) w = (x : ModGL Tag.E6 L)
        exact hwx⟩

theorem twInndiagEquivRgrp_apply {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (w : ↥(RecipeExcLang.twInndiagGroup K σ)) :
    ((twInndiagEquivRgrp hn hK σ hσ Fr hFr w : ↥(TwistedDiag.Rgrp L Fr)) : ModGL Tag.E6 L) =
      baseChangeGL (algebraMap K L) (w : ModGL TwistTag.E6.tag K) := rfl

@[expose] noncomputable def rgrpConjAut {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    ↥(TwistedDiag.Rgrp L Fr) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
  (RecipeExcLang.twConj K σ).comp
    (twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm.toMonoidHom

theorem rgrpConjAut_apply_baseChange {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (w : ↥(RecipeExcLang.twInndiagGroup K σ)) :
    rgrpConjAut hn hK σ hσ Fr hFr (twInndiagEquivRgrp hn hK σ hσ Fr hFr w) =
      RecipeExcLang.twConj K σ w := by
  rw [rgrpConjAut, MonoidHom.comp_apply]
  change (RecipeExcLang.twConj K σ)
      ((twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm
        ((twInndiagEquivRgrp hn hK σ hσ Fr hFr) w)) = RecipeExcLang.twConj K σ w
  rw [MulEquiv.symm_apply_apply]

theorem twConj_injective {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    Function.Injective (RecipeExcLang.twConj K σ) := by
  intro a b hab
  have hle := twInndiagGroup_le_twistedE6InndiagGL σ
  have h1 : twistedE6InndiagConj K σ ⟨a, hle a.2⟩ =
      twistedE6InndiagConj K σ ⟨b, hle b.2⟩ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have h2 := congrArg
      (fun φ : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) => φ h) hab
    exact congrArg Subtype.val h2
  have h2 : (⟨a, hle a.2⟩ : ↥(twistedE6InndiagGL K σ)) = ⟨b, hle b.2⟩ :=
    twistedE6InndiagConj_injective Nat.prime_two hn hK σ hσ h1
  have h3 : (a : ModGL TwistTag.E6.tag K) = (b : ModGL TwistTag.E6.tag K) :=
    congrArg (fun g : ↥(twistedE6InndiagGL K σ) => (g : ModGL TwistTag.E6.tag K)) h2
  exact Subtype.ext h3

theorem rgrpConjAut_injective {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    Function.Injective (rgrpConjAut hn hK σ hσ Fr hFr) := by
  intro x y hxy
  have h2 : (twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm x =
      (twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm y := by
    apply twConj_injective hn hK σ hσ
    change (RecipeExcLang.twConj K σ)
        ((twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm x) =
      (RecipeExcLang.twConj K σ) ((twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm y)
    exact hxy
  exact (twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm.injective h2

theorem rgrpConjAut_range {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    (rgrpConjAut hn hK σ hσ Fr hFr).range = (RecipeExcLang.twConj K σ).range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨(twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm x, rfl⟩
  · rintro _ ⟨w, rfl⟩
    refine ⟨(twInndiagEquivRgrp hn hK σ hσ Fr hFr) w, ?_⟩
    rw [rgrpConjAut, MonoidHom.comp_apply]
    change (RecipeExcLang.twConj K σ)
        ((twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm
          ((twInndiagEquivRgrp hn hK σ hσ Fr hFr) w)) = RecipeExcLang.twConj K σ w
    rw [MulEquiv.symm_apply_apply]

end Ambient

section Contract


theorem exists_rgrpAut {f : ℕ} (hf : 1 ≤ f) (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω]
    [IsAlgClosure (GaloisField 2 (2 * f)) Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ f) :
    ∃ Φ : ↥(TwistedDiag.Rgrp Ω Fr) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      Function.Injective Φ ∧ Φ.range = LayerSixE.twInndiagAut f ∧
      ∀ x (hx : x ∈ TwistedDiag.Rgrp Ω Fr),
        x ∈ TwistedDiag.Cgrp (GaloisField 2 (2 * f)) (frobQ 2 f) Ω →
        Φ ⟨x, hx⟩ ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6
          (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
          MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range := by
  classical
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : GaloisField 2 (2 * f), frobQEquiv hf c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  refine ⟨rgrpConjAut hf hK (frobQEquiv hf) hσ Fr hFr,
    rgrpConjAut_injective hf hK (frobQEquiv hf) hσ Fr hFr, ?_, ?_⟩
  · refine Eq.trans (rgrpConjAut_range (L := Ω) hf hK (frobQEquiv hf) hσ Fr hFr) ?_
    rw [LayerSixE.twInndiagAut]
    exact (inn_sup_compatParamAut_eq_range_twConj (K := GaloisField 2 (2 * f))
      (σ := frobQEquiv hf)).symm
  · intro x hx hxC
    obtain ⟨c, hc, hcx⟩ := hxC
    set c₀ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
      ⟨c, hc⟩ with hc₀
    have hcΓ : (c₀ : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f)) (frobQEquiv hf) :=
      RecipeExcLang.graphFixedRootGroup_le_twInndiag (frobQEquiv hf) c₀.2
    set e := twInndiagEquivRgrp hf hK (frobQEquiv hf) hσ Fr hFr with he
    have h1 : e ⟨c₀, hcΓ⟩ = ⟨x, hx⟩ := by
      refine Subtype.ext ?_
      change (baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)) c = x
      exact hcx
    have hval : rgrpConjAut hf hK (frobQEquiv hf) hσ Fr hFr ⟨x, hx⟩ = MulAut.conj c₀ := by
      rw [← h1, rgrpConjAut_apply_baseChange]
      exact RecipeExcLang.twConj_of_mem_C0 (frobQEquiv hf) c₀
    exact ⟨c₀, hval.symm⟩

end Contract

end CFSG.StandardType.NoOffTwE6Three
