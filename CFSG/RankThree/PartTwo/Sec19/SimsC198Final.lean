module

public import CFSG.RankThree.PartTwo.Sec19.Step198Proof
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Main
import CFSG.RankThree.PartTwo.Sec19.SimsC198Transport
import CFSG.RankThree.PartTwo.Sec19.SimsC198Descent
import CFSG.RankThree.PartTwo.Sec19.Step1914E
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Mult
import CFSG.Adapters.TauCetiExceptional.EvenD4

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem odd_card_center_of_pCore_two_eq_bot {X : Type} [Group X] [Finite X]
    (h : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center X) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 2 h2
  have hle : Subgroup.zpowers (z : X) ≤ Subgroup.center X :=
    Subgroup.zpowers_le.mpr z.2
  haveI : (Subgroup.zpowers (z : X)).Normal := Subgroup.normal_of_le_center hle
  have hz' : orderOf (z : X) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hp : IsPGroup 2 (Subgroup.zpowers (z : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz', pow_one])
  have hzle : Subgroup.zpowers (z : X) ≤ CFSG.pCore 2 X := le_sSup ⟨inferInstance, hp⟩
  have hzb : (z : X) ∈ CFSG.pCore 2 X := hzle (Subgroup.mem_zpowers _)
  rw [h, Subgroup.mem_bot] at hzb
  rw [hzb, orderOf_one] at hz'
  exact absurd hz' (by norm_num)

private theorem theta_eq_pCore_two_of_simple {I : Type} [Group I] [Finite I]
    [IsSimpleGroup (I ⧸ CFSG.pCore 2 I)] [Group.IsPerfect (I ⧸ CFSG.pCore 2 I)] :
    aschbacherSolvableCore 3 I = CFSG.pCore 2 I := by
  refine theta_eq_pCore_two_of_solvable fun N hN hs => ?_
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    have hsolv : Group.IsSolvable (I ⧸ CFSG.pCore 2 I) :=
      Group.isSolvable_of_surjective
        (f := ((Subgroup.topEquiv : (⊤ : Subgroup (I ⧸ CFSG.pCore 2 I)) ≃*
          (I ⧸ CFSG.pCore 2 I)) : (⊤ : Subgroup (I ⧸ CFSG.pCore 2 I)) →* (I ⧸ CFSG.pCore 2 I)))
        Subgroup.topEquiv.surjective
    exact Group.IsPerfect.not_isSolvable (I ⧸ CFSG.pCore 2 I) hsolv

private theorem congr_thetaQuotMulAut {K : Type} [Group K] [Finite K]
    (h : aschbacherSolvableCore 3 K = CFSG.pCore 2 K) (σ : MulAut K) :
    MulAut.congr (QuotientGroup.quotientMulEquivOfEq h) (Sec4.thetaQuotMulAut K σ) =
      Transport.pCoreQuotMulAut K σ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

private theorem exists_model
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F),
      Nat.card F = (2 ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ 2 ^ q.exponent) ∧
        Nonempty ((TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group ≃*
          CFSG.Blueprint.DerivedCentralQuotient
            (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 F σ.toRingHom)) ∧
        Nonempty ((TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group ≃*
          graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := by
  have hm1 : 1 ≤ q.exponent := q.exponent_pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (3 * q.exponent)) = (2 ^ q.exponent) ^ TwistTag.D4.order := by
    rw [GaloisField.card 2 (3 * q.exponent) (by omega), ← pow_mul, mul_comm]
    rfl
  obtain ⟨σ, hσ, -, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hm1
    (GaloisField 2 (3 * q.exponent)) hK
  have hKq : Nat.card (GaloisField 2 (3 * q.exponent)) = q.card ^ TwistTag.D4.order := by
    rw [TauCeti.PrimePower.card_def, hq2]
    exact hK
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq2 _ hKq
    σ.toRingHom (fun x => by rw [TauCeti.PrimePower.card_def, hq2]; exact hσ x)
  have e₃ := CFSG.TauCetiBridge.Twisted.nativeEquiv (t := TwistTag.D4)
    (σ := σ.toRingHom) Nat.prime_two hm1 hK hσ
  exact ⟨GaloisField 2 (3 * q.exponent), inferInstance, inferInstance, σ, hK, hσ, ⟨e₂.symm⟩,
    ⟨e₂.symm.trans e₃⟩⟩

theorem census198_of_main
    (h : MainCensus) : Census198 := by
  intro G _ _ K L D c hKD hO2 hKp hKq hDK hDab hD9 hfaith hLK hcL hcD hc3 hLc hLsn hLp hLq htype
    hDL
  have hX : RankHyp (K ⧸ CFSG.pCore 2 K) := rankHyp_of_census hKD hO2 hKq
  obtain ⟨hAut, hcZ⟩ :=
    autDatum_of_census hDK hDab hD9 hfaith hLK hcL hcD hc3 hLc hLsn hLp hLq htype hDL
  obtain ⟨⟨q, hv, hq2, ⟨e⟩⟩, φ, hφ𝒟, hφ⟩ := h _ hX _ _ _ (AutDatum.descent hX.quasisimple hAut hcZ)
  obtain ⟨F, _, _, σ, hF, hσ, ⟨eD⟩, ⟨eG⟩⟩ := exists_model hv hq2
  have hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ :=
    CFSG.ComponentClassification.RankTwoExceptional.D4.center_eq_bot_of_d4 q.exponent_pos hF σ hσ
      hX.quasisimple.1.commutator_eq_top (odd_card_center_of_pCore_two_eq_bot hX.pCore_two)
      (e.trans eG)
  let εZ : K ⧸ CFSG.pCore 2 K ≃* (K ⧸ CFSG.pCore 2 K) ⧸ Subgroup.center (K ⧸ CFSG.pCore 2 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  haveI : IsSimpleGroup ((K ⧸ CFSG.pCore 2 K) ⧸ Subgroup.center (K ⧸ CFSG.pCore 2 K)) :=
    hX.quasisimple.2.1
  haveI : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) := εZ.isSimpleGroup
  haveI : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := hX.quasisimple.1
  have hθ : aschbacherSolvableCore 3 K = CFSG.pCore 2 K := theta_eq_pCore_two_of_simple
  let eX : K ⧸ CFSG.pCore 2 K ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := εZ.trans e
  refine ⟨⟨2, q.exponent, ⟨Nat.prime_two, q.exponent_pos, rfl⟩, F, inferInstance, inferInstance, hF,
    σ.toRingHom, hσ, ⟨eX.trans eD⟩⟩, q.exponent, q.exponent_pos, F, inferInstance, inferInstance,
    hF, σ, hσ, ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans (eX.trans eG)⟩, ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ𝒟
  obtain ⟨d, hd, hdD, rfl⟩ := mem_actImage hψ
  refine ⟨d, hdD, hd, ?_⟩
  rintro ⟨z, hz⟩
  apply hφ
  have hq : quotAct K ⟨d, hd⟩ = MulAut.conj (QuotientGroup.quotientMulEquivOfEq hθ z) := by
    have h1 := congr_thetaQuotMulAut hθ (Sec4.compAction K ⟨d, hd⟩)
    rw [← hz, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at h1
    exact h1.symm
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hθ z : K ⧸ CFSG.pCore 2 K) :
    (K ⧸ CFSG.pCore 2 K) ⧸ Subgroup.center (K ⧸ CFSG.pCore 2 K)), ?_⟩
  rw [hq, centerQuotAut_conj]

end CFSG.RankThree.PartTwo.Sec19.SimsC198
