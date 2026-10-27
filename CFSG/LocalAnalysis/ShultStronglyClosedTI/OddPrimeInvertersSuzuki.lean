module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersFrobenius
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiInvolutions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzukiTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddPrimeInverters

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

theorem suzuki_card_coprime {q : ℕ} (hq : Even q) (hq1 : 1 ≤ q) :
    Nat.Coprime (q - 1) ((q ^ 2 + 1) * q ^ 2) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hr : Odd r := by
    rcases Nat.even_or_odd r with h | h
    · exact absurd hq (Nat.not_even_iff_odd.mpr h.add_one)
    · exact h
  refine Nat.Coprime.mul_right ?_
    (Nat.Coprime.pow_right 2 (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right r)))
  rw [show (r + 1) ^ 2 + 1 = (r + 2) * r + 2 by ring, Nat.coprime_mul_right_add_right]
  exact Nat.coprime_two_right.mpr hr

variable (m : ℕ)

theorem suzuki_commutator_eq_top (hm : 1 ≤ m) : commutator (SuzukiMatrixGroup m) = ⊤ :=
  (IsSimpleBenderGroupAtExponent.isSuzuki ⟨m, rfl, ⟨MulEquiv.refl _⟩⟩).isPerfect (by omega)

theorem suzuki_conj_eq_inv_of_frobenius
    (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ (2 * m + 1) - 1) (y g : SuzukiMatrixGroup m)
    (hy : IsPGroup p (Subgroup.zpowers y)) (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y)
    (hne : g * y * g⁻¹ ≠ y) : g * y * g⁻¹ = y⁻¹ ∨ g ^ 2 * y * (g ^ 2)⁻¹ = y⁻¹ := by
  let : Fintype (BinaryGaloisField (2 * m + 1)) := Fintype.ofFinite _
  have : Fact p.Prime := ⟨hp⟩
  have hq : Fintype.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (2 * m + 1) (by omega)
  have hdvd : orderOf y ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hy
    rw [Nat.card_zpowers] at hn
    have hG : orderOf y ∣
        (2 ^ (2 * m + 1) - 1) * (((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2) := by
      have hcard := lemma114_suzukiMatrixGroup_card_formula m (by omega)
      rw [show (2 ^ (2 * m + 1) - 1) * (((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2) =
        Nat.card (SuzukiMatrixGroup m) by rw [hcard]; ring]
      exact orderOf_dvd_natCard y
    have hc1 : Nat.Coprime (orderOf y) (2 ^ (2 * m + 1) - 1) :=
      hn ▸ Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)
    have hc2 : Nat.Coprime (orderOf y) ((2 ^ (2 * m + 1)) ^ 2) := by
      rw [hn, ← pow_mul]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact hc2.dvd_of_dvd_mul_right (hc1.dvd_of_dvd_mul_left hG)
  have hyq : y ^ (2 ^ (2 * m + 1)) ^ 2 = y⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact orderOf_dvd_iff_pow_eq_one.mp hdvd)
  refine conj_eq_inv_or_sq_conj_eq_inv_of_lt_four hyq ?_ hne
  have h := exists_lt_conj_eq_pow_card_pow_of_dvd (K := BinaryGaloisField (2 * m + 1)) (e := 1)
    (by norm_num) (SuzukiMatrixGroup m).subtype (SuzukiMatrixGroup m).subtype_injective hp hp2 hy
    (by rw [hq, pow_one]; exact hdvd) hgy
  simpa only [hq] using h

theorem suzukiMatrixGroup_oddPrimeInvertersAndSplitFusion
    (hm : 1 ≤ m) :
    OddPrimeInvertersAndSplitFusion (SuzukiMatrixGroup m) (2 ^ (2 * m + 1)) := by
  obtain ⟨-, -, -, -, -, -, -, -, w, T₀, -, -, -, -, -, hT₀, hinv⟩ :=
    suzuki_natural_action_standard_pair m hm
  have hq1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have hqeven : Even (2 ^ (2 * m + 1)) := (Nat.even_pow' (by omega)).mpr even_two
  refine oddPrimeInvertersAndSplitFusion_of_data (suzuki_commutator_eq_top m hm)
    (lemma114_suzuki_oddSylow_isCyclic_of_equiv (MulEquiv.refl _))
    (fun t ht => suzuki_involution_centralizer_isPGroup m (by omega) t ht)
    (by rw [lemma114_suzukiMatrixGroup_card_formula m (by omega)]; ring)
    (suzuki_card_coprime hqeven hq1) T₀ hT₀ w⁻¹ (fun t ht => ?_)
    (suzuki_conj_eq_inv_of_frobenius m hm)
  rw [inv_inv]
  exact hinv t ht

theorem suzukiGroup_oddPrimeInvertersAndSplitFusion
    {a : ℕ} (ha : 1 ≤ a) {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2 ^ (2 * a + 1)) :
    OddPrimeInvertersAndSplitFusion (CFSG.Blueprint.suzukiGroup a k) (Nat.card k) := by
  rw [hk]
  exact (suzukiMatrixGroup_oddPrimeInvertersAndSplitFusion a ha).of_mulEquiv
    ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a k)).trans
      ((glaSzEquivNative a ha hk).trans (suzukiCoverNativeEquiv a)))

end CFSG.ShultStronglyClosedTI.OddPrimeInverters
