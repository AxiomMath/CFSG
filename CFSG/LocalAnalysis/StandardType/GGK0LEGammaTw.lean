module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
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
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem langGamma_conj_eq_map_twistedE6RootGroup
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup TwistTag.E6.tag L p)
    (hAlg : S.IsAlgebraic) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra K L) (σ : K ≃+* K),
      Nat.card K = S.D.q ^ 2 ∧ (∀ c, σ c = c ^ S.D.q) ∧
        S.Γ.map (MulAut.conj S.D.g0).toMonoidHom =
          (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L)) := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨K, hKcard, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_exists_subfield (Ω := L) (ℓ := r) (f := e) he
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKcard]
    exact pow_ne_zero _ (pow_ne_zero _ hr.ne_zero))
  let : Fintype K := Fintype.ofFinite K
  have : CharP K r := charP_of_card_eq_prime_pow (f := e * 2)
    (by rw [← Nat.card_eq_fintype_card, hKcard, ← pow_mul])
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ (r ^ e) :=
    ⟨RingEquiv.ofBijective (iterateFrobenius K r e) ⟨(iterateFrobenius K r e).injective,
      Finite.surjective_of_injective (iterateFrobenius K r e).injective⟩,
      fun c => iterateFrobenius_def r e c⟩
  have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
  have : IsAlgClosure K L := ⟨inferInstance, ⟨fun x => by
    obtain ⟨k, hk, hx⟩ := hAlg x
    refine ⟨Polynomial.X ^ (S.D.q ^ k) - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero _ (Nat.one_lt_pow hk.ne' hq1), ?_⟩
    simp [hx]⟩⟩
  have hFr' : ∀ c, Fr c = c ^ (r ^ e) := fun c => by rw [hFr, hq]
  have hΓ := Γ_eq_map_twistedE6RootGroup hr he hKcard hσ hFr' S.D hΦ
  refine ⟨K, inferInstance, inferInstance, inferInstance, σ, by rw [hKcard, hq],
    fun c => by rw [hσ, hq], ?_⟩
  have hid : (MulAut.conj S.D.g0).toMonoidHom.comp (MulAut.conj S.D.g0⁻¹).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by simp [mul_assoc]
  rw [show S.Γ = S.D.Γ from rfl, hΓ, Subgroup.map_map, hid, Subgroup.map_id]

end CFSG.StandardType.LangRat

end
