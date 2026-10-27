module

public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

private theorem g2Arith_two_pow_eq {a b X Y : ℕ} (hX : Odd X) (hY : Odd Y)
    (h : 2 ^ a * X = 2 ^ b * Y) : a = b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX0 : X ≠ 0 := by obtain ⟨k, hk⟩ := hX; omega
  have hY0 : Y ≠ 0 := by obtain ⟨k, hk⟩ := hY; omega
  have hX2 : ¬ 2 ∣ X := by obtain ⟨k, hk⟩ := hX; omega
  have hY2 : ¬ 2 ∣ Y := by obtain ⟨k, hk⟩ := hY; omega
  have h1 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (pow_ne_zero a (by norm_num : (2 : ℕ) ≠ 0)) hX0,
    padicValNat.mul (pow_ne_zero b (by norm_num : (2 : ℕ) ≠ 0)) hY0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hX2,
    padicValNat.eq_zero_of_not_dvd hY2] at h1
  omega

private theorem g2Arith_U_odd {m : ℕ} (hm : 2 ≤ m) :
    Odd (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) * 3) := by
  have hm0 : m ≠ 0 := by omega
  have hE : 2 ∣ 2 ^ m := dvd_pow_self 2 hm0
  have hE2 : 2 ∣ (2 ^ m) ^ 2 := dvd_pow hE (by norm_num)
  have hE6 : 2 ∣ (2 ^ m) ^ 6 := dvd_pow hE (by norm_num)
  have hpos2 : 0 < (2 ^ m) ^ 2 := by positivity
  have hpos6 : 0 < (2 ^ m) ^ 6 := by positivity
  have o6 : Odd ((2 ^ m) ^ 6 - 1) := Nat.odd_iff.mpr (by omega)
  have o2 : Odd ((2 ^ m) ^ 2 - 1) := Nat.odd_iff.mpr (by omega)
  exact Nat.odd_mul.mpr ⟨Nat.odd_mul.mpr ⟨o6, o2⟩, Nat.odd_iff.mpr (by norm_num)⟩

private theorem g2Arith_V_odd {e : ℕ} (he : 1 ≤ e) :
    Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) ∧
      Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) := by
  have hE : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have hE2 : 2 ∣ (2 ^ e) ^ 2 := dvd_pow hE (by norm_num)
  have hE3 : 2 ∣ (2 ^ e) ^ 3 := dvd_pow hE (by norm_num)
  have hpos2 : 0 < (2 ^ e) ^ 2 := by positivity
  have hpos3 : 0 < (2 ^ e) ^ 3 := by positivity
  have o2 : Odd ((2 ^ e) ^ 2 - 1) := Nat.odd_iff.mpr (by omega)
  have o3 : Odd ((2 ^ e) ^ 3 - 1) := Nat.odd_iff.mpr (by omega)
  have o3' : Odd ((2 ^ e) ^ 3 + 1) := Nat.odd_iff.mpr (by omega)
  exact ⟨Nat.odd_mul.mpr ⟨o2, o3⟩, Nat.odd_mul.mpr ⟨o2, o3'⟩⟩

private theorem g2Arith_two_exp {m e V : ℕ} (hm : 2 ≤ m) (hV : Odd V)
    (h : (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) * 3 = (2 ^ e) ^ 3 * V) :
    e = 2 * m := by
  have key : 2 ^ (6 * m) * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) * 3) = 2 ^ (3 * e) * V := by
    rw [show (2 : ℕ) ^ (6 * m) = (2 ^ m) ^ 6 by ring,
      show (2 : ℕ) ^ (3 * e) = (2 ^ e) ^ 3 by ring]
    calc (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) * 3)
        = (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) * 3 := by ring
      _ = (2 ^ e) ^ 3 * V := h
  have h6m : 6 * m = 3 * e := g2Arith_two_pow_eq (g2Arith_U_odd hm) hV key
  omega

private theorem g2Arith_D {q : ℕ} (hq : 4 ≤ q) : ∃ D, 15 ≤ D ∧ q ^ 2 = D + 1 := by
  have h16 : 16 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  exact ⟨q ^ 2 - 1, by omega, by omega⟩

private theorem g2Arith_expand {q D : ℕ} (hD : q ^ 2 = D + 1) :
    q ^ 6 = (D + 1) ^ 3 ∧ q ^ 6 - 1 = D * (D ^ 2 + 3 * D + 3) ∧ q ^ 2 - 1 = D := by
  have h6 : q ^ 6 = (D + 1) ^ 3 := by rw [← hD]; ring
  refine ⟨h6, ?_, by omega⟩
  rw [h6]
  apply Nat.sub_eq_of_eq_add
  ring

private theorem g2Arith_pure_L3 {q : ℕ} (hq : 4 ≤ q)
    (h : q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) * 3 =
      (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 - 1))) : False := by
  obtain ⟨D, hD15, hD⟩ := g2Arith_D hq
  obtain ⟨h6, hs6, hs2⟩ := g2Arith_expand hD
  have hs4 : (D + 1) ^ 2 - 1 = D * (D + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  have hs3 : (D + 1) ^ 3 - 1 = D * (D ^ 2 + 3 * D + 3) := by
    apply Nat.sub_eq_of_eq_add; ring
  have key : (D + 1) ^ 3 * (D * (D ^ 2 + 3 * D + 3) * D * 3)
      = (D + 1) ^ 3 * (D * (D + 2) * (D * (D ^ 2 + 3 * D + 3))) := by
    calc (D + 1) ^ 3 * (D * (D ^ 2 + 3 * D + 3) * D * 3)
        = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) * 3 := by rw [hs6, hs2, h6]; ring
      _ = (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 - 1)) := h
      _ = (D + 1) ^ 3 * (D * (D + 2) * (D * (D ^ 2 + 3 * D + 3))) := by
        rw [hD, hs4, hs3]
  have hK : 0 < (D + 1) ^ 3 * D * (D ^ 2 + 3 * D + 3) * D :=
    mul_pos (mul_pos (mul_pos (pow_pos (by omega) 3) (by omega)) (by omega)) (by omega)
  have key2 : (D + 1) ^ 3 * D * (D ^ 2 + 3 * D + 3) * D * 3
      = (D + 1) ^ 3 * D * (D ^ 2 + 3 * D + 3) * D * (D + 2) := by
    calc (D + 1) ^ 3 * D * (D ^ 2 + 3 * D + 3) * D * 3
        = (D + 1) ^ 3 * (D * (D ^ 2 + 3 * D + 3) * D * 3) := by ring
      _ = (D + 1) ^ 3 * (D * (D + 2) * (D * (D ^ 2 + 3 * D + 3))) := key
      _ = (D + 1) ^ 3 * D * (D ^ 2 + 3 * D + 3) * D * (D + 2) := by ring
  have h32 : 3 = D + 2 := Nat.eq_of_mul_eq_mul_left hK key2
  omega

private theorem g2Arith_pure_U3 {q : ℕ} (hq : 4 ≤ q)
    (h : q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) * 3 =
      (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 + 1))) : False := by
  obtain ⟨D, hD15, hD⟩ := g2Arith_D hq
  obtain ⟨h6, hs6, hs2⟩ := g2Arith_expand hD
  have hs4 : (D + 1) ^ 2 - 1 = D * (D + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  have key : (D + 1) ^ 3 * (D * (D ^ 2 + 3 * D + 3) * D * 3)
      = (D + 1) ^ 3 * (D * (D + 2) * ((D + 1) ^ 3 + 1)) := by
    calc (D + 1) ^ 3 * (D * (D ^ 2 + 3 * D + 3) * D * 3)
        = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) * 3 := by rw [hs6, hs2, h6]; ring
      _ = (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 + 1)) := h
      _ = (D + 1) ^ 3 * (D * (D + 2) * ((D + 1) ^ 3 + 1)) := by
        rw [hD, hs4]
  have hK : 0 < (D + 1) ^ 3 * D := mul_pos (pow_pos (by omega) 3) (by omega)
  have key2 : (D + 1) ^ 3 * D * ((D ^ 2 + 3 * D + 3) * D * 3)
      = (D + 1) ^ 3 * D * ((D + 2) * ((D + 1) ^ 3 + 1)) := by
    calc (D + 1) ^ 3 * D * ((D ^ 2 + 3 * D + 3) * D * 3)
        = (D + 1) ^ 3 * (D * (D ^ 2 + 3 * D + 3) * D * 3) := by ring
      _ = (D + 1) ^ 3 * (D * (D + 2) * ((D + 1) ^ 3 + 1)) := key
      _ = (D + 1) ^ 3 * D * ((D + 2) * ((D + 1) ^ 3 + 1)) := by ring
  have h32 : (D ^ 2 + 3 * D + 3) * D * 3 = (D + 2) * ((D + 1) ^ 3 + 1) :=
    Nat.eq_of_mul_eq_mul_left hK key2
  have hD3 : D ≤ D ^ 3 := Nat.le_self_pow (by norm_num) D
  nlinarith [h32, hD3, Nat.zero_le (D ^ 4)]

private theorem g2Arith_core {p e D S : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hD : 15 ≤ D)
    (hpt : ¬ p ∣ D + 1) (hS : S ≤ 2 * (p ^ e) ^ 5)
    (hEq : (p ^ e) ^ 3 * S = 3 * (D + 1) ^ 3 * (D ^ 2 * (D ^ 2 + 3 * D + 3))) : False := by
  have hp3' : ¬ p ∣ 3 := fun h3 => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  have hcop0 : Nat.Coprime p (3 * (D + 1) ^ 3) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h3 | h3
    · exact hp3' h3
    · exact hpt (hp.dvd_of_dvd_pow h3)
  have hcop : Nat.Coprime ((p ^ e) ^ 3) (3 * (D + 1) ^ 3) :=
    Nat.Coprime.pow_left 3 (Nat.Coprime.pow_left e hcop0)
  have hdvd : (p ^ e) ^ 3 ∣ 3 * (D + 1) ^ 3 * (D ^ 2 * (D ^ 2 + 3 * D + 3)) := ⟨S, hEq.symm⟩
  have hdvd' : (p ^ e) ^ 3 ∣ D ^ 2 * (D ^ 2 + 3 * D + 3) := hcop.dvd_of_dvd_mul_left hdvd
  have hbd : (p ^ e) ^ 3 ≤ 2 * (D + 1) ^ 2 := by
    by_cases hpD : p ∣ D
    · have hpC : ¬ p ∣ D ^ 2 + 3 * D + 3 := by
        intro hC
        have hdD : p ∣ D * (D + 3) := dvd_mul_of_dvd_left hpD _
        have hC' : D ^ 2 + 3 * D + 3 = D * (D + 3) + 3 := by ring
        rw [hC'] at hC
        exact hp3' ((Nat.dvd_add_right hdD).mp hC)
      have hcopC : Nat.Coprime ((p ^ e) ^ 3) (D ^ 2 + 3 * D + 3) :=
        Nat.Coprime.pow_left 3 (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpC))
      have h1 : (p ^ e) ^ 3 ∣ D ^ 2 := hcopC.dvd_of_dvd_mul_right hdvd'
      have h2 : (p ^ e) ^ 3 ≤ D ^ 2 := Nat.le_of_dvd (pow_pos (by omega) 2) h1
      nlinarith
    · have hcopD : Nat.Coprime ((p ^ e) ^ 3) (D ^ 2) :=
        Nat.Coprime.pow_left 3 (Nat.Coprime.pow_left e
          (Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpD)))
      have h1 : (p ^ e) ^ 3 ∣ D ^ 2 + 3 * D + 3 := hcopD.dvd_of_dvd_mul_left hdvd'
      have h2 : (p ^ e) ^ 3 ≤ D ^ 2 + 3 * D + 3 := Nat.le_of_dvd (by omega) h1
      nlinarith
  have hlow : (D + 1) ^ 7 ≤ (p ^ e) ^ 3 * S := by
    rw [hEq]
    have h1 : (D + 1) ^ 2 ≤ 3 * D ^ 2 := by nlinarith
    have h2 : (D + 1) ^ 2 ≤ D ^ 2 + 3 * D + 3 := by nlinarith
    calc (D + 1) ^ 7 = (D + 1) ^ 3 * (D + 1) ^ 2 * (D + 1) ^ 2 := by ring
      _ ≤ (D + 1) ^ 3 * (3 * D ^ 2) * (D ^ 2 + 3 * D + 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h2
      _ = 3 * (D + 1) ^ 3 * (D ^ 2 * (D ^ 2 + 3 * D + 3)) := by ring
  have hup : (p ^ e) ^ 3 * S ≤ 2 * (p ^ e) ^ 8 := by
    calc (p ^ e) ^ 3 * S ≤ (p ^ e) ^ 3 * (2 * (p ^ e) ^ 5) := Nat.mul_le_mul le_rfl hS
      _ = 2 * (p ^ e) ^ 8 := by ring
  have hA : ((D + 1) ^ 7) ^ 3 ≤ ((p ^ e) ^ 3 * S) ^ 3 := Nat.pow_le_pow_left hlow 3
  have hB : ((p ^ e) ^ 3 * S) ^ 3 ≤ (2 * (p ^ e) ^ 8) ^ 3 := Nat.pow_le_pow_left hup 3
  have hC : ((p ^ e) ^ 3) ^ 8 ≤ (2 * (D + 1) ^ 2) ^ 8 := Nat.pow_le_pow_left hbd 8
  have key : (D + 1) ^ 21 ≤ 2048 * (D + 1) ^ 16 := by
    calc (D + 1) ^ 21 = ((D + 1) ^ 7) ^ 3 := by ring
      _ ≤ ((p ^ e) ^ 3 * S) ^ 3 := hA
      _ ≤ (2 * (p ^ e) ^ 8) ^ 3 := hB
      _ = 8 * ((p ^ e) ^ 3) ^ 8 := by ring
      _ ≤ 8 * (2 * (D + 1) ^ 2) ^ 8 := Nat.mul_le_mul le_rfl hC
      _ = 2048 * (D + 1) ^ 16 := by ring
  have hmul : (D + 1) ^ 16 * (D + 1) ^ 5 ≤ (D + 1) ^ 16 * 2048 := by
    calc (D + 1) ^ 16 * (D + 1) ^ 5 = (D + 1) ^ 21 := by ring
      _ ≤ 2048 * (D + 1) ^ 16 := key
      _ = (D + 1) ^ 16 * 2048 := by ring
  have h5 : (D + 1) ^ 5 ≤ 2048 := Nat.le_of_mul_le_mul_left hmul (by positivity)
  have h16 : 16 ^ 5 ≤ (D + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h16' : (16 : ℕ) ^ 5 ≤ 2048 := le_trans h16 h5
  norm_num at h16'

private theorem g2Arith_odd {m p e S : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hp3 : p ≠ 3)
    (hp2 : p ≠ 2) (hS : S ≤ 2 * (p ^ e) ^ 5)
    (h : (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) * 3 = (p ^ e) ^ 3 * S) :
    False := by
  have hq4 : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  obtain ⟨D, hD15, hD⟩ := g2Arith_D hq4
  obtain ⟨h6, hs6, hs2⟩ := g2Arith_expand hD
  have hpt : ¬ p ∣ D + 1 := by
    rw [← hD]
    intro hd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hEq : (p ^ e) ^ 3 * S = 3 * (D + 1) ^ 3 * (D ^ 2 * (D ^ 2 + 3 * D + 3)) := by
    rw [← h, hs6, hs2, h6]
    ring
  exact g2Arith_core hp hp3 hD15 hpt hS hEq

theorem g2_mul_three_ne_L3 {m p e : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    CFSG.Open.ordG2 (2 ^ m) * 3 ≠ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
  intro h
  unfold CFSG.Open.ordG2 at h
  have hq4 : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  by_cases hp2 : p = 2
  · subst hp2
    have he2 : e = 2 * m := g2Arith_two_exp hm (g2Arith_V_odd he).1 h
    subst he2
    rw [show (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 by ring] at h
    exact g2Arith_pure_L3 hq4 h
  · have hS : ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) ≤ 2 * (p ^ e) ^ 5 := by
      calc ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) ≤ (p ^ e) ^ 2 * (p ^ e) ^ 3 :=
            Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
        _ = (p ^ e) ^ 5 := by ring
        _ ≤ 2 * (p ^ e) ^ 5 := by omega
    exact g2Arith_odd hm hp hp3 hp2 hS h

theorem g2_mul_three_ne_U3 {m p e : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    CFSG.Open.ordG2 (2 ^ m) * 3 ≠ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
  intro h
  unfold CFSG.Open.ordG2 at h
  have hq4 : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  by_cases hp2 : p = 2
  · subst hp2
    have he2 : e = 2 * m := g2Arith_two_exp hm (g2Arith_V_odd he).2 h
    subst he2
    rw [show (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 by ring] at h
    exact g2Arith_pure_U3 hq4 h
  · have hpe : 0 < (p ^ e) ^ 3 := pow_pos (pow_pos hp.pos e) 3
    have hS : ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) ≤ 2 * (p ^ e) ^ 5 := by
      calc ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) ≤ (p ^ e) ^ 2 * (2 * (p ^ e) ^ 3) :=
            Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
        _ = 2 * (p ^ e) ^ 5 := by ring
    exact g2Arith_odd hm hp hp3 hp2 hS h

theorem g2two_L3 {N r : ℕ} (hN : N ∣ 12096) (hr2 : 2 ≤ r) (hr3 : r % 3 = 1)
    (h : N * 3 = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1))) : False := by
  have hN' : N ≤ 12096 := Nat.le_of_dvd (by norm_num) hN
  have hr4 : 4 ≤ r := by omega
  have h16 : 16 ≤ r ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hr4 2)
  have h64 : 64 ≤ r ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hr4 3)
  have h15 : 15 ≤ r ^ 2 - 1 := by omega
  have h63 : 63 ≤ r ^ 3 - 1 := by omega
  have hA : 15 * 63 ≤ (r ^ 2 - 1) * (r ^ 3 - 1) := Nat.mul_le_mul h15 h63
  have hB : 64 * (15 * 63) ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := Nat.mul_le_mul h64 hA
  omega

theorem g2two_U3 {N r : ℕ} (hN : N ∣ 12096) (hr2 : 2 ≤ r) (hr3 : r % 3 = 2)
    (h : N * 3 = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1))) : r = 2 := by
  have hN' : N ≤ 12096 := Nat.le_of_dvd (by norm_num) hN
  by_contra hne
  have hr5 : 5 ≤ r := by omega
  have h25 : 25 ≤ r ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hr5 2)
  have h125 : 125 ≤ r ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hr5 3)
  have h24 : 24 ≤ r ^ 2 - 1 := by omega
  have h126 : 126 ≤ r ^ 3 + 1 := by omega
  have hA : 24 * 126 ≤ (r ^ 2 - 1) * (r ^ 3 + 1) := Nat.mul_le_mul h24 h126
  have hB : 125 * (24 * 126) ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) := Nat.mul_le_mul h125 hA
  omega

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
