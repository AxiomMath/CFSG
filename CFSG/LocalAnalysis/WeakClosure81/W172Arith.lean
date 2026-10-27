module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Arith
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem w172_geom_sum_odd {p a : ℕ} (hp : Odd p) (ha : Odd a) :
    Odd (∑ i ∈ Finset.range a, p ^ i) := by
  rw [Nat.odd_iff]
  have h : ∀ n : ℕ, (∑ i ∈ Finset.range n, p ^ i) % 2 = n % 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.1 (Odd.pow hp : Odd (p ^ n))]
      omega
  rw [h]
  exact Nat.odd_iff.mp ha

theorem w172_padicValNat_geom_sum {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : Even a)
    (ha0 : a ≠ 0) :
    padicValNat 2 (∑ i ∈ Finset.range a, p ^ i) + 1 = padicValNat 2 (p + 1) + padicValNat 2 a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have h2p : ¬ 2 ∣ p := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  have hSpos : 0 < ∑ i ∈ Finset.range a, p ^ i := by
    apply Finset.sum_pos
    · intro i _
      exact pow_pos hp.pos i
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hSne : (∑ i ∈ Finset.range a, p ^ i) ≠ 0 := hSpos.ne'
  have hgeom : ∑ i ∈ Finset.range a, p ^ i = (p ^ a - 1) / (p - 1) :=
    Nat.geomSum_eq hp.two_le a
  have hdvd : p - 1 ∣ p ^ a - 1 := Nat.sub_one_dvd_pow_sub_one p a
  have hmul : padicValNat 2 (p - 1) + padicValNat 2 (∑ i ∈ Finset.range a, p ^ i)
      = padicValNat 2 (p ^ a - 1) := by
    have hprod : (p - 1) * (∑ i ∈ Finset.range a, p ^ i) = p ^ a - 1 := by
      rw [hgeom, Nat.mul_div_cancel' hdvd]
    rw [← hprod, padicValNat.mul (p := 2) (by omega) hSne]
  have hlift := padicValNat.pow_two_sub_one (x := p) (n := a) hp1 h2p ha0 ha
  omega

theorem w172_padicValNat_succ_le_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValNat 2 (p + 1) ≤ orderOf (2 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.succ_le_two_pow_orderOf (p := p) hp2
  have hdvd : 2 ^ padicValNat 2 (p + 1) ∣ p + 1 := pow_padicValNat_dvd
  have h2 := Nat.le_of_dvd (by omega : 0 < p + 1) hdvd
  have h3 : 2 ^ padicValNat 2 (p + 1) ≤ 2 ^ orderOf (2 : ZMod p) := h2.trans hle
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3

theorem w172_arith_false {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a k c : ℕ} (ha : 1 ≤ a)
    (hk : 1 ≤ k) (hc : 2 * k ≤ c) (hdvd : 2 ^ c ∣ ∑ i ∈ Finset.range a, p ^ i)
    (h2 : a = 2 → 2 * orderOf (2 : ZMod p) ≤ 2 * k)
    (h3 : 3 ≤ a → 16 * a * orderOf (2 : ZMod p) ≤ 27 * (2 * k)) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have ho2 : 2 ≤ orderOf (2 : ZMod p) := by
    have hle := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.succ_le_two_pow_orderOf (p := p) hp2
    have hp4 : 4 ≤ p + 1 := by omega
    have hpow : 2 ^ 2 ≤ 2 ^ orderOf (2 : ZMod p) := by
      calc 2 ^ 2 = 4 := by norm_num
        _ ≤ p + 1 := hp4
        _ ≤ 2 ^ orderOf (2 : ZMod p) := hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow
  rcases Nat.even_or_odd a with haeven | haodd
  · rcases eq_or_ne a 2 with ha2 | ha2
    · subst ha2
      have hS : ∑ i ∈ Finset.range 2, p ^ i = p + 1 := by
        rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
        omega
      rw [hS] at hdvd
      have hle : 2 ^ c ≤ 2 ^ orderOf (2 : ZMod p) := by
        have h1 : 2 ^ c ≤ p + 1 := Nat.le_of_dvd (by omega) hdvd
        exact h1.trans
          (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.succ_le_two_pow_orderOf (p := p) hp2)
      have hco : c ≤ orderOf (2 : ZMod p) :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
      have h2o : 2 * orderOf (2 : ZMod p) ≤ 2 * k := h2 rfl
      omega
    · have ha4 : 4 ≤ a := by
        obtain ⟨m, hm⟩ := haeven
        omega
      have ha0 : a ≠ 0 := by omega
      have hSpos : 0 < ∑ i ∈ Finset.range a, p ^ i := by
        apply Finset.sum_pos
        · intro i _
          exact pow_pos hp.pos i
        · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
      have hSne : (∑ i ∈ Finset.range a, p ^ i) ≠ 0 := hSpos.ne'
      have hcS : c ≤ padicValNat 2 (∑ i ∈ Finset.range a, p ^ i) :=
        (padicValNat_dvd_iff_le hSne).mp hdvd
      have hpe := w172_padicValNat_geom_sum hp hp2 haeven ha0
      have hb := w172_padicValNat_succ_le_orderOf hp hp2
      have hv2 : padicValNat 2 a + 2 ≤ a := padicValNat_add_le_self (p := 2) (a := a) (by omega)
      have hcLe : c + 1 ≤ orderOf (2 : ZMod p) + padicValNat 2 a := by
        have h1 : c + 1 ≤ padicValNat 2 (∑ i ∈ Finset.range a, p ^ i) + 1 := by omega
        rw [hpe] at h1
        omega
      have h2k : 2 * k ≤ orderOf (2 : ZMod p) + padicValNat 2 a := by omega
      have h3a : 16 * a * orderOf (2 : ZMod p) ≤ 27 * (2 * k) := h3 (by omega)
      have hMain : 16 * a * orderOf (2 : ZMod p) ≤
          27 * orderOf (2 : ZMod p) + 27 * padicValNat 2 a := by
        have h1 : 16 * a * orderOf (2 : ZMod p)
            ≤ 27 * (orderOf (2 : ZMod p) + padicValNat 2 a) :=
          h3a.trans (Nat.mul_le_mul_left 27 h2k)
        have heq : 27 * (orderOf (2 : ZMod p) + padicValNat 2 a)
            = 27 * orderOf (2 : ZMod p) + 27 * padicValNat 2 a := by omega
        rwa [heq] at h1
      have hA : (16 * a - 27) * orderOf (2 : ZMod p) ≤ 27 * padicValNat 2 a := by
        have hsub : (16 * a - 27) * orderOf (2 : ZMod p)
            = 16 * a * orderOf (2 : ZMod p) - 27 * orderOf (2 : ZMod p) :=
          Nat.sub_mul _ _ _
        rw [hsub]
        have hle := Nat.sub_le_sub_right hMain (27 * orderOf (2 : ZMod p))
        have heq : 27 * orderOf (2 : ZMod p) + 27 * padicValNat 2 a
            - 27 * orderOf (2 : ZMod p) = 27 * padicValNat 2 a := by omega
        rwa [heq] at hle
      have hstep : 32 * a - 54 ≤ 27 * padicValNat 2 a := by
        have h2le : (16 * a - 27) * 2 ≤ (16 * a - 27) * orderOf (2 : ZMod p) :=
          Nat.mul_le_mul_left _ ho2
        have h2eq : (16 * a - 27) * 2 = 32 * a - 54 := by
          rw [Nat.sub_mul]
          omega
        rw [h2eq] at h2le
        exact h2le.trans hA
      have h27v : 27 * padicValNat 2 a + 54 ≤ 27 * a := by
        have h := Nat.mul_le_mul_left 27 hv2
        have heq : 27 * (padicValNat 2 a + 2) = 27 * padicValNat 2 a + 54 := by omega
        rwa [heq] at h
      have hfin : 32 * a ≤ 27 * a := by
        have h54 : 54 ≤ 32 * a := by omega
        have h := Nat.add_le_add_right hstep 54
        rw [Nat.sub_add_cancel h54] at h
        exact h.trans h27v
      omega
  · have hc1 : 1 ≤ c := by omega
    have hSodd : Odd (∑ i ∈ Finset.range a, p ^ i) := w172_geom_sum_odd hpodd haodd
    have h2dvd : 2 ∣ ∑ i ∈ Finset.range a, p ^ i := by
      have h : 2 ^ 1 ∣ 2 ^ c := pow_dvd_pow 2 hc1
      simpa using h.trans hdvd
    exact hSodd.not_two_dvd_nat h2dvd

end CFSG.LocalAnalysis.WeakClosure81

end
