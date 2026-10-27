module

public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem k1566l7b_padicValNat_three_pow_three_sub_one {q : ℕ} (hq : q % 3 = 1)
    (hq1 : 1 < q) : padicValNat 3 (q ^ 3 - 1) = padicValNat 3 (q - 1) + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd 3 := by decide
  have hdvd : 3 ∣ q - 1 := by omega
  have hnd : ¬ 3 ∣ q := by omega
  have h := padicValNat.pow_sub_pow (p := 3) (x := q) (y := 1) hodd hq1 hdvd hnd
    (by norm_num : (3 : ℕ) ≠ 0)
  rw [one_pow, padicValNat_self] at h
  exact h

private theorem k1566l7b_padicValNat_sq_add {q : ℕ} (hq : q % 3 = 1) :
    padicValNat 3 (q ^ 2 + q + 1) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  have hne : 3 * t ^ 2 + 3 * t + 1 ≠ 0 := by positivity
  have e : (3 * t + 1) ^ 2 + (3 * t + 1) + 1 = 3 * (3 * t ^ 2 + 3 * t + 1) := by ring
  rw [e, padicValNat.mul (by norm_num) hne, padicValNat_self]
  have h3 : padicValNat 3 (3 * t ^ 2 + 3 * t + 1) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd ?_
    intro h
    have h1 : (3 : ℤ) ∣ 3 * (t : ℤ) ^ 2 + 3 * (t : ℤ) + 1 := by exact_mod_cast h
    omega
  rw [h3, add_zero]

private theorem k1566l7b_mod_eq_one_l7o {q : ℕ} (hq : (q : ZMod 3) = ((1 : ℤ) : ZMod 3)) :
    q % 3 = 1 := by
  have h1 : (q : ZMod 3) = ((1 : ℕ) : ZMod 3) := by rw [hq]; norm_num
  exact (ZMod.natCast_eq_natCast_iff q 1 3).mp h1

private theorem k1566l7b_mod_eq_two_l7o {q : ℕ} (hq : (q : ZMod 3) = ((-1 : ℤ) : ZMod 3)) :
    q % 3 = 2 := by
  have h1 : (q : ZMod 3) = ((2 : ℕ) : ZMod 3) := by
    rw [hq]
    have hcast : ((2 : ℕ) : ZMod 3) = ((2 : ℤ) : ZMod 3) := by norm_num
    rw [hcast, ZMod.intCast_eq_intCast_iff]
    decide
  exact (ZMod.natCast_eq_natCast_iff q 2 3).mp h1

private theorem k1566l7b_padicValNat_D4_order_l7o {q a : ℕ} (hq2 : 2 ≤ q)
    (hqmod : q % 3 = 1 ∨ q % 3 = 2) (h2 : padicValNat 3 (q ^ 2 - 1) = a) :
    padicValNat 3 (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) =
      2 * a + 2 := by
  have hq2mod : q ^ 2 % 3 = 1 := by
    rcases hqmod with h | h <;> rw [Nat.pow_mod, h]
  have hq4mod : q ^ 4 % 3 = 1 := by
    rcases hqmod with h | h <;> rw [Nat.pow_mod, h]
  have h3q : ¬ 3 ∣ q := by rcases hqmod with h | h <;> omega
  have hne0 : q ^ 12 ≠ 0 := by positivity
  have hne1 : q ^ 2 - 1 ≠ 0 := by
    have h : 1 < q ^ 2 := by nlinarith
    omega
  have hne2 : q ^ 6 - 1 ≠ 0 := by
    have h := Nat.pow_le_pow_right (show 0 < q by omega) (show 2 ≤ 6 by norm_num)
    have h1 : 1 < q ^ 2 := by nlinarith
    omega
  have hne3 : q ^ 8 + q ^ 4 + 1 ≠ 0 := by positivity
  have h12 : padicValNat 3 (q ^ 12) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd h3q, mul_zero]
  have h6 : padicValNat 3 (q ^ 6 - 1) = a + 1 := by
    have h := k1566l7b_padicValNat_three_pow_three_sub_one (q := q ^ 2) hq2mod (by nlinarith)
    rw [show (q ^ 2) ^ 3 = q ^ 6 by ring, h2] at h
    exact h
  have h8 : padicValNat 3 (q ^ 8 + q ^ 4 + 1) = 1 := by
    have h := k1566l7b_padicValNat_sq_add (q := q ^ 4) hq4mod
    rw [show (q ^ 4) ^ 2 + q ^ 4 + 1 = q ^ 8 + q ^ 4 + 1 by ring] at h
    exact h
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero hne0 hne1) hne2) hne3,
    padicValNat.mul (mul_ne_zero hne0 hne1) hne2, padicValNat.mul hne0 hne1,
    h12, h2, h6, h8]
  ring

private theorem k1566l7b_D4_order_one_l7o {p f q : ℕ} (hq2 : 2 ≤ q) (hqdef : q = p ^ f)
    (hqmod : q % 3 = 1) :
    padicValNat 3 (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) =
      2 * padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - 1)) + 2 := by
  have hqZ : (q : ℤ) = (p : ℤ) ^ f := by
    rw [hqdef]
    push_cast
    ring
  have ha : Int.natAbs ((p : ℤ) ^ f - 1) = q - 1 := by
    have hcast : (p : ℤ) ^ f - 1 = ((q - 1 : ℕ) : ℤ) := by
      rw [← hqZ, Nat.cast_sub (by omega : 1 ≤ q)]
      ring
    rw [hcast, Int.natAbs_natCast]
  have h2 : padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q - 1) := by
    have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h := Nat.sq_sub_sq q 1
      rw [one_pow, Nat.mul_comm] at h
      exact h
    rw [hfac, padicValNat.mul (by omega) (by omega)]
    have h1 : padicValNat 3 (q + 1) = 0 := by
      refine padicValNat.eq_zero_of_not_dvd ?_
      omega
    rw [h1, add_zero]
  rw [ha]
  exact k1566l7b_padicValNat_D4_order_l7o hq2 (Or.inl hqmod) h2

private theorem k1566l7b_D4_order_two_l7o {p f q : ℕ} (hq2 : 2 ≤ q) (hqdef : q = p ^ f)
    (hqmod : q % 3 = 2) :
    padicValNat 3 (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) =
      2 * padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - (-1))) + 2 := by
  have hqZ : (q : ℤ) = (p : ℤ) ^ f := by
    rw [hqdef]
    push_cast
    ring
  have ha : Int.natAbs ((p : ℤ) ^ f - (-1)) = q + 1 := by
    have hcast : (p : ℤ) ^ f - (-1) = ((q + 1 : ℕ) : ℤ) := by
      rw [← hqZ]
      push_cast
      ring
    rw [hcast, Int.natAbs_natCast]
  have h2 : padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) := by
    have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h := Nat.sq_sub_sq q 1
      rw [one_pow, Nat.mul_comm] at h
      exact h
    rw [hfac, padicValNat.mul (by omega) (by omega)]
    have h1 : padicValNat 3 (q - 1) = 0 := by
      refine padicValNat.eq_zero_of_not_dvd ?_
      omega
    rw [h1, zero_add]
  rw [ha]
  exact k1566l7b_padicValNat_D4_order_l7o hq2 (Or.inr hqmod) h2

theorem padicValNat_card_graphFixedRootGroup_D4 {K : Type}
    [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) :
    padicValNat 3 (Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
      2 * padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) + 2 := by
  set q := p ^ f with hqdef
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hqZ : (q : ZMod 3) = (eps : ZMod 3) := by
    rw [hqdef]
    push_cast
    exact hq
  have hcard : Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) := by
    have h := (triality_both_orientations_exact_finite_order p f hp hf K hK 1 (Or.inl rfl)
      σ.toRingHom (fun c => by simpa using hσ c)).1
    rw [← hqdef] at h
    exact h
  rw [hcard]
  rcases heps with rfl | rfl
  · have hqmod : q % 3 = 1 := k1566l7b_mod_eq_one_l7o hqZ
    exact k1566l7b_D4_order_one_l7o hq2 hqdef hqmod
  · have hqmod : q % 3 = 2 := k1566l7b_mod_eq_two_l7o hqZ
    exact k1566l7b_D4_order_two_l7o hq2 hqdef hqmod

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7
