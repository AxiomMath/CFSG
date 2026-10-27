module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
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
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigidLang
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidModels
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
import CFSG.RankThree.PartOne.KE.SLnShape
import CFSG.RankThree.PartOne.KGD.D4QA1

public section

namespace CFSG.StandardType.TwE6D5Core

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem exists_langSetup_ofTwist_twE6_spec {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hK2 : ringChar K = 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0 : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) :
    ∃ S : LangSetup Tag.E6 (AlgebraicClosure K) 5,
      S.D = LangDatum.ofTwist TwistTag.E6 Fr q hFr v hg0 hlang ∧
      ((MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (twistedE6RootGroup K σ).subtype)).range = S.Γ ∧
      (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = v • permLattice TwistTag.E6.perm γ) ∧
      ∀ x ∈ twistedE6InndiagGL K σ,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g0 ∈
          torusGroup TwistTag.E6.tag (AlgebraicClosure K) →
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g0 ∈ S.D.torus := by
  haveI : CharP K 2 := ringChar.of_eq hK2
  obtain ⟨f, hf, rfl⟩ : ∃ f, 1 ≤ f ∧ q = 2 ^ f := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hcard : q ^ 2 = 2 ^ (n : ℕ) := by rw [← hK, Nat.card_eq_fintype_card, hn]
    have hdvd : q ∣ 2 ^ (n : ℕ) := hcard ▸ dvd_pow_self q two_ne_zero
    obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    refine ⟨f, Nat.one_le_iff_ne_zero.2 fun h0 => ?_, hqf⟩
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, hqf, h0] at h1
    norm_num at h1
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let D : LangDatum TwistTag.E6.tag (AlgebraicClosure K) :=
    LangDatum.ofTwist TwistTag.E6 Fr (2 ^ f) hFr v hg0 hlang
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved _ _ D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 := by
    refine ⟨Nat.prime_two.isPrimePow.pow (by omega), ?_⟩
    change ((2 ^ f : ℕ) : AlgebraicClosure K) = 0
    rw [Nat.cast_pow, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_pow (by omega)]
  have hpq : ¬ 5 ∣ D.q :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 (Nat.Coprime.pow_right f (by norm_num))
  have hfin : Finite D.model := finite_model_twistedE6 Nat.prime_two hf hK hσ hFr D rfl
  refine ⟨D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hfin, rfl, ?_,
    fun γ hγ => frobRootMap_ofTwist_apply (by positivity) hFr hg0 hlang hρ hγ, fun x hx hxT => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
    exact (Γ_eq_map_twistedE6RootGroup Nat.prime_two hf hK hσ hFr D rfl).symm
  · have hfix : twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) x) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) x :=
      (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hf hK σ hσ Fr hFr
        ⟨x, hx, rfl⟩).2
    refine mem_twistedTorusOf.2 ⟨hxT, ?_⟩
    change canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v *
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g0) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)⁻¹ =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g0
    rw [map_mul, map_mul, map_inv, hlang, hfix]
    group

theorem exists_langSetup_of_twE6Frame {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hK2 : ringChar K = 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0 : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {t : ModGL TwistTag.E6.tag K} (ht : t ∈ twistedE6InndiagGL K σ)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (hta : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
      rootDiagUnit TwistTag.E6.tag a) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = q ∧ S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (twistedE6InndiagConj K σ ⟨t, ht⟩ c) =
        rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      (∀ c : ↥(twistedE6RootGroup K σ), ι c = g0⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g0) ∧
      (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = v • permLattice TwistTag.E6.perm γ) ∧
      S.D = LangDatum.ofTwist TwistTag.E6 Fr q hFr v hg0 hlang := by
  obtain ⟨S, hSD, hrange, hρ, htorus⟩ :=
    exists_langSetup_ofTwist_twE6_spec σ hK hσ hK2 hFr hg0 hlang
  have hT : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 ∈ S.D.torus :=
    htorus t ht (by rw [hta]; exact rootDiagUnit_mem_torusGroup a)
  rw [hta] at hT
  let ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (twistedE6RootGroup K σ).subtype)
  have hι : ∀ c : ↥(twistedE6RootGroup K σ), ι c = g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g0 :=
    fun c => by
      change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c : ModGL TwistTag.E6.tag K)) = _
      rw [MulAut.conj_apply, inv_inv]
  refine ⟨S, ι, congrArg LangDatum.q hSD, congrArg LangDatum.Φ hSD, hT,
    (MulAut.conj g0⁻¹).injective.comp
      ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _)), hrange, fun c => ?_, hι,
    hρ, hSD⟩
  rw [hι, hι]
  change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (t * (c : ModGL TwistTag.E6.tag K) * t⁻¹) * g0 =
    rootDiagUnit TwistTag.E6.tag a * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c : ModGL TwistTag.E6.tag K) * g0) * (rootDiagUnit TwistTag.E6.tag a)⁻¹
  rw [map_mul, map_mul, map_inv, ← hta]
  group

end CFSG.StandardType.TwE6D5Core

end
