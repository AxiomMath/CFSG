module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralMax
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSylowTorus
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.TwistedE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Hard


@[expose] def GGOrdPToralTwE6RestHard : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → ((p = 3 ∧ 3 ∣ 2 ^ f - 1) ∨ (p = 5 ∧ 5 ∣ 2 ^ f + 1)) →
    (∃ A : Subgroup (twistedE6Group 2 f), IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (twistedE6Group 2 f) p

end Hard

section Adjoint


theorem sylowTorus_or_card_lt_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ ℓ ^ f) (hp5 : 5 ≤ p)
    (h5 : p = 5 → ¬ 5 ∣ ℓ ^ f - 1 ∧ ¬ 5 ∣ ℓ ^ f + 1) :
    (∃ m, SylowTorus (twistedE6RootGroup K σ) p m) ∨
      ∀ A : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p A → Nat.card A < p ^ 4 := by
  have hp1 : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp2' : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  by_cases h7 : 7 ≤ p
  · by_cases hc : 3 ≤ degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p))
    · exact Or.inl (CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sylowTorus_twistedE6
        hℓ hf K hK σ hσ hp h7 hpq hc)
    · refine Or.inr fun A hA => ?_
      by_cases h1c : degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p)) ≤ 1
      · have hle := rankLE1_twistedE6 hℓ hf K hK σ hσ hp hpq h1c A hA
        rw [pow_one] at hp1
        omega
      · have h2c : degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p)) = 2 := by omega
        obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
        rw [he] at h2c
        rcases degCountTw_eq_two h2c with rfl | rfl
        · have hle := (sylowTorus_twistedE6_three hℓ hf K hK σ hσ hp he).rankLE2 hp le_rfl A hA
          omega
        · have hle := (sylowTorus_twistedE6_four hℓ hf K hK σ hσ hp he).rankLE2 hp le_rfl A hA
          omega
  · have hp5' : p = 5 := by
      have h6 : p ≤ 6 := by omega
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    subst hp5'
    obtain ⟨h1, h2⟩ := h5 rfl
    refine Or.inr fun A hA => ?_
    have he3 := PRankBounds.three_le_orderOf hp hpq (Nat.one_le_pow _ _ hℓ.pos) h1 h2
    have : Fact (Nat.Prime 5) := ⟨hp⟩
    have hdvd : orderOf (((ℓ ^ f : ℕ)) : ZMod 5) ∣ 5 - 1 :=
      ZMod.orderOf_dvd_card_sub_one fun h0 => hpq ((ZMod.natCast_eq_zero_iff _ _).1 h0)
    obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod 5) = e := ⟨_, rfl⟩
    rw [he] at hdvd he3
    have he4 : e = 4 := by
      have hle : e ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases e
      · exact absurd hdvd (by decide)
      · rfl
    subst he4
    have hle := (sylowTorus_twistedE6_four hℓ hf K hK σ hσ hp he).rankLE2 hp le_rfl A hA
    omega

end Adjoint

section Transport


theorem ggOrdPToralMax_graphFixedRootGroup_of_sylowTorus {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {θ : K →+* K} (hθ : σ.toRingHom = θ) {p m : ℕ}
    (h : SylowTorus (twistedE6RootGroup K σ) p m) :
    GGOrdPToralMax ↥(graphFixedRootGroup TwistTag.E6 K θ) p := by
  subst hθ
  haveI : Finite (Module.End K (RootModule TwistTag.E6.tag K)) := Module.finite_of_finite K
  exact OrdPInnerExc.ggOrdPToralMax_of_sylowTorus h

theorem card_lt_graphFixedRootGroup_of_card_lt {K : Type} [Field K] {σ : K ≃+* K}
    {θ : K →+* K} (hθ : σ.toRingHom = θ) {p N : ℕ}
    (h : ∀ A : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p A → Nat.card A < N) :
    ∀ A : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K θ), IsElemAbelian p A →
      Nat.card A < N := by
  subst hθ
  exact h

end Transport

section Reduction


theorem ggOrdPToralTwE6Rest_of_hard (h : GGOrdPToralTwE6RestHard) : GGOrdPToralTwE6Rest := by
  intro f p hf hp hp2 h3 h5 hA
  by_cases hhard : (p = 3 ∧ 3 ∣ 2 ^ f - 1) ∨ (p = 5 ∧ 5 ∣ 2 ^ f + 1)
  · exact h f p hf hp hhard hA
  have hp3 : p ≠ 3 := by
    rintro rfl
    refine hhard (Or.inl ⟨rfl, ?_⟩)
    have hx : ¬ 3 ∣ 2 ^ f := fun hd =>
      absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hn : ¬ 3 ∣ 2 ^ f + 1 := fun hd => h3 ⟨rfl, hd⟩
    omega
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  have hpq : ¬ p ∣ 2 ^ f := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨π, hπ, hkerπ, -, -⟩ := LayerSixE.exists_model_twistedE6 hf
  have hcop : Nat.Coprime (Nat.card π.ker) p := by
    rw [hkerπ]
    exact OrdPInnerExc.coprime_card_center_twistedE6 ggTwE6CenterTrivialInput_holds hf hp h3
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  have h5' : p = 5 → ¬ 5 ∣ 2 ^ f - 1 ∧ ¬ 5 ∣ 2 ^ f + 1 := by
    rintro rfl
    exact ⟨fun hd => h5 ⟨le_rfl, hd⟩, fun hd => hhard (Or.inr ⟨rfl, hd⟩)⟩
  have : Finite (GaloisField 2 (2 * f)) := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ two_ne_zero))
  rcases sylowTorus_or_card_lt_twistedE6 Nat.prime_two hf (GaloisField 2 (2 * f)) hK
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ hp hpq hp5 h5' with ⟨m, hm⟩ | hlt
  · exact OrdPInnerExc.ggOrdPToralMax_of_surjective hp hπ hkerπ.le hcop
      (ggOrdPToralMax_graphFixedRootGroup_of_sylowTorus hσθ hm)
  · obtain ⟨A, hAel, hAc⟩ := hA
    have : Finite (Module.End (GaloisField 2 (2 * f))
      (RootModule TwistTag.E6.tag (GaloisField 2 (2 * f)))) :=
      Module.finite_of_finite (GaloisField 2 (2 * f))
    exact absurd hAc (not_le.2 (OrdPInnerExc.card_lt_of_card_lt_map hcop
      (card_lt_graphFixedRootGroup_of_card_lt hσθ hlt) hAel))

end Reduction

end CFSG.StandardType
