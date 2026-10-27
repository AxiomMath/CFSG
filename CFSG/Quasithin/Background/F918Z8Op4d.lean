module

public import CFSG.Quasithin.Background.F918Z8Op4a1
import CFSG.CGT.T75N.PpdCyclic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersSuzuki
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.OddPrimeInverters
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
open CFSG.CGT.T75N

theorem opq4d_exists_mulEquiv_suzukiMatrixGroup {X : Type} [Group X] {n : ℕ} (hX : IsSz n X) :
    ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧ Nonempty (X ≃* SuzukiMatrixGroup m) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  exact ⟨a, ha, rfl, ⟨e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      ((glaSzEquivNative a ha hK).trans (suzukiCoverNativeEquiv a)))⟩⟩

theorem opq4d_card_suzukiMatrixGroup {m : ℕ} (hm : 0 < m) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := fun x =>
    iterateFrobeniusEquiv_def K 2 (m + 1) x
  rcases External.huppert_blackburn_XI_3_3 m hm pi hpi with ⟨_, _, _, _, _, _, hcard, _⟩
  exact hcard

theorem opq4d_ppd {q p : ℕ} (hq : 1 ≤ q) (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ q ^ 2 + 1) :
    p ∣ q ^ 4 - 1 ∧ ∀ k, 0 < k → k < 4 → ¬ p ∣ q ^ k - 1 := by
  have hsq : (q : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) p).mpr h
    push_cast at this
    exact this
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h0'))
  refine ⟨?_, fun k hk0 hk4 hdiv => ?_⟩
  · refine (ZMod.natCast_eq_zero_iff _ p).mp ?_
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    push_cast
    linear_combination ((q : ZMod p) ^ 2 - 1) * hsq
  · have hdiv' := (ZMod.natCast_eq_zero_iff _ p).mpr hdiv
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)] at hdiv'
    push_cast at hdiv'
    apply h2
    interval_cases k
    · linear_combination hsq - ((q : ZMod p) + 1) * hdiv'
    · linear_combination hsq - hdiv'
    · linear_combination (1 - ((q : ZMod p) - 1) * q) * hsq + ((q : ZMod p) - 1) * hdiv'

theorem opq4d_isCyclic_of_isPGroup {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (T₀ : Subgroup (SuzukiMatrixGroup m)) [IsCyclic T₀] (hT₀ : Nat.card T₀ = 2 ^ (2 * m + 1) - 1)
    (P : Subgroup (SuzukiMatrixGroup m)) (hP : IsPGroup p P) : IsCyclic P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hbot : P = ⊥
  · subst hbot
    infer_instance
  have hq1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have hcard := opq4d_card_suzukiMatrixGroup (m := m) (by omega)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hbot (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  have hpP : p ∣ Nat.card P := hn ▸ dvd_pow_self p hn0
  have hpX : p ∣ ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) :=
    hcard ▸ hpP.trans (Subgroup.card_subgroup_dvd_card P)
  have hpq : ¬ p ∣ 2 ^ (2 * m + 1) := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  by_cases hpq1 : p ∣ 2 ^ (2 * m + 1) - 1
  · refine isCyclic_of_isPGroup_of_cyclic_hall T₀
      (M := ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2) ?_ ?_ P hP
    · rw [hcard, hT₀]
      ring
    · intro hM
      rcases hp.dvd_mul.1 hM with h | h
      · exact (opq4d_ppd hq1 hp hp2 h).2 1 (by norm_num) (by norm_num) (by simpa using hpq1)
      · exact hpq (hp.dvd_of_dvd_pow h)
  · have hp' : p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
      rcases hp.dvd_mul.1 hpX with h | h
      · rcases hp.dvd_mul.1 h with h' | h'
        · exact h'
        · exact absurd (hp.dvd_of_dvd_pow h') hpq
      · exact absurd h hpq1
    obtain ⟨hpn, hnp⟩ := opq4d_ppd hq1 hp hp2 hp'
    have : Fintype (BinaryGaloisField (2 * m + 1)) := Fintype.ofFinite _
    have hcardF : Fintype.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 (2 * m + 1) (by omega)
    refine isCyclic_of_isPGroup_of_embed (n := 4) (F := BinaryGaloisField (2 * m + 1))
      (SuzukiMatrixGroup m).subtype Subtype.val_injective (by norm_num) ?_ ?_ P hP
    · rw [hcardF]
      exact hpn
    · intro k hk0 hk4
      rw [hcardF]
      exact hnp k hk0 hk4

theorem opq4d_conj_eq_inv_of_frobenius {m : ℕ} (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ (2 * m + 1) - 1) (y g : SuzukiMatrixGroup m)
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
      have hcard := opq4d_card_suzukiMatrixGroup (m := m) (by omega)
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

theorem opq4d_suzuki_exists_involution_inverts {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (S : Sylow p (SuzukiMatrixGroup m))
    (hS1 : (S : Subgroup (SuzukiMatrixGroup m)) ≠ ⊥) :
    ∃ s : SuzukiMatrixGroup m, s * s = 1 ∧
      ∀ x ∈ (S : Subgroup (SuzukiMatrixGroup m)), s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, w, T₀, -, -, -, -, hcyc, hT₀, hinv⟩ :=
    suzuki_natural_action_standard_pair m hm
  have hq1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have hqeven : Even (2 ^ (2 * m + 1)) := (Nat.even_pow' (by omega)).mpr even_two
  refine opq4a_exists_involution_inverts_sylow (q := 2 ^ (2 * m + 1))
    (N := ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2) (suzuki_commutator_eq_top m hm)
    (fun r hr hr2 P => ?_)
    (fun t ht => suzuki_involution_centralizer_isPGroup m (by omega) t ht)
    (by rw [opq4d_card_suzukiMatrixGroup (by omega)]; ring)
    (suzuki_card_coprime hqeven hq1) T₀ hT₀ w⁻¹ (fun t ht => ?_)
    (opq4d_conj_eq_inv_of_frobenius hm) hp hp2 S hS1
  · exact opq4d_isCyclic_of_isPGroup hm hr.out hr2 T₀ hT₀ P P.isPGroup'
  · rw [inv_inv]
    exact hinv t ht

theorem a38_invSyl_sz {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (hL : IsSz n ↥L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card L) : InvSylAll L p := by
  obtain ⟨m, hm, -, ⟨e⟩⟩ := opq4d_exists_mulEquiv_suzukiMatrixGroup hL
  exact opq4a_invSylAll_of_mulEquiv e hp hpL
    (fun S hS1 => opq4d_suzuki_exists_involution_inverts hm hp hp2 S hS1)

end CFSG.Quasithin
