module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofCore
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenCyclotomicTori
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG.Blueprint.Chevalley
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KF83GTwoTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ g : adjointGroup .G2 K, orderOf g ≠ 9

theorem center_specialLinearGroup_two_eq_bot {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have hsq : (r - 1) ^ 2 = 0 := by
      have e : (r - 1) ^ 2 = r ^ 2 + 1 - 2 * r := by ring
      rw [e, hr2, h2, zero_mul, sub_zero]
      have e2 : (1 : F) + 1 = 2 := by norm_num
      rw [e2, h2]
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hsq)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

theorem exists_orderOf_projSL_two_eq (m : ℕ) (hm : 1 ≤ m) :
    ∃ x : projSL 2 (GaloisField 2 m), orderOf x = 2 ^ m + 1 := by
  obtain ⟨A, hA⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := GaloisField 2 m)
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  set π := QuotientGroup.mk'
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))) with hπ
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk',
      center_specialLinearGroup_two_eq_bot]
  refine ⟨(Sec4.projSLEquivPSL (GaloisField 2 m)).symm (π A), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_injective π hinj, hA, hcard]

theorem pow_three_add_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have h : q ≤ q ^ 2 := by nlinarith
  zify [h]
  ring

theorem exists_prime_dvd_phi_six (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 ∧ p ∣ 2 ^ (3 * n) + 1 := by
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * n) (by omega)
    (by omega)
  have h6 : 0 < 6 * n := by omega
  have hQ : p ∣ 2 ^ (3 * n) + 1 := by
    refine (hp.dvd_add_one_iff h6 (3 * n)).mpr ⟨⟨1, by ring⟩, ?_⟩
    rintro ⟨t, ht⟩
    rcases t with _ | t
    · omega
    · nlinarith
  have hq : ¬ p ∣ 2 ^ n + 1 := by
    intro h
    obtain ⟨⟨t, ht⟩, -⟩ := (hp.dvd_add_one_iff h6 n).mp h
    rcases t with _ | t
    · omega
    · nlinarith
  have hfac : 2 ^ (3 * n) + 1 = (2 ^ n + 1) * ((2 ^ n) ^ 2 - 2 ^ n + 1) := by
    rw [← pow_three_add_one_eq (2 ^ n) Nat.one_le_two_pow, ← pow_mul, mul_comm n 3]
  have hd : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := by
    rw [hfac] at hQ
    exact (hp.prime.dvd_mul.mp hQ).resolve_left hq
  have hp2 : p ≠ 2 := hp.ne_two h6
  have hp3 : p ≠ 3 := fun h3 => by
    have := hp.eq_two_of_dvd_three h6 (by rw [h3])
    omega
  have hp5 : 3 < p := by
    have := hp.prime.two_le
    omega
  exact ⟨p, hp.prime, hp5, hd, hQ⟩


theorem orderOf_ne_of_two_le (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (y : adjointGroup .G2 K) : orderOf y ≠ 2 ^ (3 * n) + 1 := by
  intro hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨p, hp, hp3, hpd, hpQ⟩ := exists_prime_dvd_phi_six n hn
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 ^ n := ⟨_, rfl⟩
  rw [← hq] at hK hpd
  have hq1 : 1 ≤ q := hq ▸ Nat.one_le_two_pow
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hfac : 2 ^ (3 * n) + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    rw [← pow_three_add_one_eq q hq1, hq, ← pow_mul, mul_comm n 3]
  have hdz : ((q ^ 2 - q + 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 + (-1) * (Nat.card K : ℤ) + 1 := by
    rw [hK, Nat.cast_add, Nat.cast_sub hqq]
    push_cast
    ring
  obtain ⟨T, -, -, -, -, hcent⟩ :=
    CFSG.RankThree.Chevalley.even_G2_cyclotomic_three_six_tori_and_prime_centralizers K (-1)
      (Or.inl rfl) (q ^ 2 - q + 1) hdz hp hp3 hpd
  obtain ⟨k, hk⟩ := hpQ
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact absurd hk (Nat.succ_ne_zero _)
  have hxo : orderOf (y ^ k) = p := by
    rw [orderOf_pow_of_dvd hk0 (by rw [hy, hk]; exact dvd_mul_left k p), hy, hk,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  obtain ⟨-, -, -, hcard, -⟩ := hcent (y ^ k) hxo
  have hle : Subgroup.zpowers y ≤ Subgroup.centralizer ({y ^ k} : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.pow_right (Commute.refl y) k).eq
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, hy, hcard, hfac] at hdvd
  have hpos : 0 < q ^ 2 - q + 1 := by omega
  have hle' := Nat.le_of_dvd hpos hdvd
  nlinarith

theorem kF83IndepGTwo_of_two (h : KF83GTwoTwo) : KF83IndepGTwo := by
  intro K _ _ n hn hK H
  refine ⟨fun e => ?_⟩
  obtain ⟨y, hy⟩ := exists_orderOf_projSL_two_eq (3 * n) (by have := hn.pos; omega)
  have hy' : orderOf ((e.symm y : H) : adjointGroup .G2 K) = 2 ^ (3 * n) + 1 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  rcases (show n = 1 ∨ 2 ≤ n by have := hn.pos; omega) with rfl | hn2
  · exact h K (by rw [hK]; norm_num) _ (by rw [hy']; norm_num)
  · exact orderOf_ne_of_two_le K hn2 hK _ hy'

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
