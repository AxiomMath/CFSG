module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.Defs
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.Adapters.TauCetiExceptional.EvenD4
import CFSG.ClassicalInvolution.Orders.Twisted
import CFSG.ClassicalInvolution.Orders.Symplectic
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.RankThree.PartTwo.Sec11.KSListsProof

open CFSG.Open (ordTrialityD4 ordG2)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Carriers


theorem card_G2_carrier (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group = ordG2 q.card := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hb : Nonempty (AdjointQuotient .G2 (GaloisField q.p q.exponent) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
    by_cases hp : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp _ hK
    · exact CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp _ hK
  obtain ⟨e⟩ := hb
  exact CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2
    ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hK, ⟨e.symm⟩⟩


theorem card_trialityD4_carrier (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group = ordTrialityD4 q.card := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm : 0 < TwistTag.D4.order := by decide
  have hK : Nat.card (GaloisField q.p (q.exponent * TwistTag.D4.order)) =
      q.card ^ TwistTag.D4.order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hm.ne'),
      TauCeti.PrimePower.card_def, pow_mul]
  let σ := iterateFrobenius (GaloisField q.p (q.exponent * TwistTag.D4.order)) q.p q.exponent
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [iterateFrobenius_def, TauCeti.PrimePower.card_def]
  have hK' : Nat.card (GaloisField q.p (q.exponent * TwistTag.D4.order)) =
      (q.p ^ q.exponent) ^ TwistTag.D4.order := by rw [hK, TauCeti.PrimePower.card_def]
  have hσ' : ∀ x, σ x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [hσ, TauCeti.PrimePower.card_def]
  rw [TauCeti.PrimePower.card_def]
  by_cases hp : q.p = 2
  · obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hp _ hK σ hσ
    have h : TwistedChevalleyModel (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group .D4
        (2 ^ q.exponent) := by
      rw [← hp]
      exact ⟨_, inferInstance, inferInstance, hK', σ, hσ', ⟨e.symm⟩⟩
    rw [hp]
    exact CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two q.exponent_pos h
  · obtain ⟨e⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp _ hK σ hσ
    exact CFSG.ClassicalInvolution.card_of_twistedChevalleyModel_D4_of_ne_two q.prime_p hp
      q.exponent_pos ⟨_, inferInstance, inferInstance, hK', σ, hσ', ⟨e.symm⟩⟩

end Carriers

noncomputable def projSLEquiv (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projSL n K :=
  (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSL n K))

theorem card_projSL_two_mul (K : Type) [Field K] [Finite K] :
    Nat.card (projSL 2 K) * Nat.gcd 2 (Nat.card K - 1) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2)
    (by norm_num)
  rw [Nat.card_congr (projSLEquiv 2 K).toEquiv] at h
  have hN : Nat.card K ^ (2 * (2 - 1) / 2) * ∏ j ∈ Finset.Icc 2 2, (Nat.card K ^ j - 1) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [show 2 * (2 - 1) / 2 = 1 from rfl, show Finset.Icc 2 2 = ({2} : Finset ℕ) by decide,
      Finset.prod_singleton, pow_one]
  rw [h, hN]
  exact Nat.div_mul_cancel
    (Dvd.dvd.mul_left ((Nat.gcd_dvd_right 2 _).trans (Nat.sub_one_dvd_pow_sub_one _ 2)) _)

theorem card_projSL_four_mul (K : Type) [Field K] [Finite K] :
    Nat.card (projSL 4 K) * Nat.gcd 4 (Nat.card K - 1) =
      Nat.card K ^ 6 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1)) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 4)
    (by norm_num)
  rw [Nat.card_congr (projSLEquiv 4 K).toEquiv] at h
  have hN : Nat.card K ^ (4 * (4 - 1) / 2) * ∏ j ∈ Finset.Icc 2 4, (Nat.card K ^ j - 1) =
      Nat.card K ^ 6 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1)) := by
    rw [show 4 * (4 - 1) / 2 = 6 from rfl,
      show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num), mul_assoc]
  rw [h, hN]
  exact Nat.div_mul_cancel (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    ((Nat.gcd_dvd_right 4 _).trans (Nat.sub_one_dvd_pow_sub_one _ 2)) _) _) _)

theorem card_projSU_four_mul (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    Nat.card (projSU 4 p f) * Nat.gcd 4 (p ^ f + 1) =
      (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) := by
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (n := 4)
    (by norm_num)
  rw [Nat.card_congr ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU 4 p f))).toEquiv]
    at h
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  have hq4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow _ _ hq
  have h2 : ((((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2)).toNat = (p ^ f) ^ 2 - 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hq2]
      ring, Int.toNat_natCast]
  have h3 : ((((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3)).toNat = (p ^ f) ^ 3 + 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) by
      push_cast
      ring, Int.toNat_natCast]
  have h4 : ((((p ^ f : ℕ) : ℤ) ^ 4 - (-1) ^ 4)).toNat = (p ^ f) ^ 4 - 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 4 - (-1) ^ 4 = (((p ^ f) ^ 4 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hq4]
      ring, Int.toNat_natCast]
  have hN : (p ^ f) ^ (4 * (4 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 4, ((((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i)).toNat =
      (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) := by
    rw [show 4 * (4 - 1) / 2 = 6 from rfl,
      show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num), h2, h3, h4, mul_assoc]
  have hdvd : p ^ f + 1 ∣ (p ^ f) ^ 4 - 1 := by
    have e : (p ^ f) ^ 4 - 1 = (p ^ f + 1) * ((p ^ f - 1) * ((p ^ f) ^ 2 + 1)) := by
      zify [hq, hq4]
      ring
    rw [e]
    exact Dvd.intro _ rfl
  rw [h, hN]
  exact Nat.div_mul_cancel
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right 4 _).trans hdvd) _) _)

theorem card_projSp_two_mul (K : Type) [Field K] [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (projSp 2 K) * 2 = Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
  have h := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero h2 (n := 2)
    (by norm_num)
  rw [Nat.card_congr ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 2 K))).toEquiv]
    at h
  rw [h, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  norm_num

end CFSG.RankThree.PartTwo.Sec11.KSListsProof
