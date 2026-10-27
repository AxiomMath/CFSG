module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.CharacterTheory.BrauerLinearThree.LocalRecognition
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem eq_of_two_pow_mul_odd {a b m m' : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : 2 ^ a * m = 2 ^ b * m') : a = b := by
  have hv := congrArg (padicValNat 2) h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) (by rintro rfl; exact (Nat.not_odd_zero hm)),
    padicValNat.mul (by positivity) (by rintro rfl; exact (Nat.not_odd_zero hm')),
    padicValNat.prime_pow, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.odd_iff.mp hm; omega),
    padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.odd_iff.mp hm'; omega)] at hv
  omega

theorem odd_two_pow_sub_one {e : ℕ} (he : 1 ≤ e) : Odd (2 ^ e - 1) := by
  have h2 : Even (2 ^ e) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) h2 odd_one

theorem card_SL3_eq {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    ∃ m, Odd m ∧ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 2 ^ (3 * n) * m := by
  refine ⟨(Nat.card K ^ 3 - 1) * (Nat.card K ^ 2 - 1), ?_, ?_⟩
  · rw [hK, ← pow_mul, ← pow_mul]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  · rw [CFSG.BrauerLinearThree.card_SL_three, mul_assoc, hK, ← pow_mul, mul_comm n 3]

theorem card_Sp4_eq {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    ∃ m, Odd m ∧ Nat.card ↥(StatedSp 2 K) = 2 ^ (4 * n) * m := by
  refine ⟨(Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1), ?_, ?_⟩
  · rw [hK, ← pow_mul, ← pow_mul]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  · rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI, Finset.prod_pair (by norm_num), hK, ← pow_mul]
    ring_nf

theorem card_G2_eq (hG2 : FactG2DerivedOrder) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ m, Odd m ∧ Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ = 2 ^ (6 * n) * m := by
  refine ⟨((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1), ?_, ?_⟩
  · rw [← pow_mul, ← pow_mul]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  · rw [hG2 K n hn hK, ← pow_mul, mul_comm n 6]

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ}

theorem kind_not_SL3_Sp4 (hn : 1 ≤ n) (h1 : KindSL3 L V n) (h2 : KindSp4 L V n) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h1
  obtain ⟨K', _, _, hK', ⟨e'⟩⟩ := h2
  obtain ⟨m, hm, hc⟩ := card_SL3_eq hn hK
  obtain ⟨m', hm', hc'⟩ := card_Sp4_eq hn hK'
  have h := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e'.toEquiv)
  rw [hc, hc'] at h
  have := eq_of_two_pow_mul_odd hm hm' h
  omega

theorem kind_not_SL3_G2 (hG2 : FactG2DerivedOrder) (hn : 2 ≤ n) (h1 : KindSL3 L V n)
    (h2 : KindG2 L V n) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h1
  obtain ⟨K', _, _, hK', ⟨e'⟩⟩ := h2
  obtain ⟨m, hm, hc⟩ := card_SL3_eq (by omega) hK
  obtain ⟨m', hm', hc'⟩ := card_G2_eq hG2 hn hK'
  have h := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e'.toEquiv)
  rw [hc, hc'] at h
  have := eq_of_two_pow_mul_odd hm hm' h
  omega

theorem kind_not_Sp4_G2 (hG2 : FactG2DerivedOrder) (hn : 2 ≤ n) (h1 : KindSp4 L V n)
    (h2 : KindG2 L V n) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h1
  obtain ⟨K', _, _, hK', ⟨e'⟩⟩ := h2
  obtain ⟨m, hm, hc⟩ := card_Sp4_eq (by omega) hK
  obtain ⟨m', hm', hc'⟩ := card_G2_eq hG2 hn hK'
  have h := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e'.toEquiv)
  rw [hc, hc'] at h
  have := eq_of_two_pow_mul_odd hm hm' h
  omega

end CFSG.Quasithin.Vol2.Ch11.SecA
