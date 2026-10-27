module

public import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

private theorem l3pi_F_mono {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) < b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1)) := by
  have h0 : 0 < a ^ 3 := pow_pos (by omega) 3
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have h1 : a ^ 3 < b ^ 3 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2' : a ^ 2 - 1 < b ^ 2 - 1 := by omega
  have h3' : a ^ 3 - 1 < b ^ 3 - 1 := by omega
  exact mul_lt_mul'' h1 (mul_lt_mul'' h2' h3' (Nat.zero_le _) (Nat.zero_le _))
    (Nat.zero_le _) (Nat.zero_le _)

private theorem l3pi_H_mono {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 + 1)) < b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 + 1)) := by
  have h0 : 0 < a ^ 3 := pow_pos (by omega) 3
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have h1 : a ^ 3 < b ^ 3 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2' : a ^ 2 - 1 < b ^ 2 - 1 := by omega
  have h3' : a ^ 3 + 1 < b ^ 3 + 1 := by omega
  exact mul_lt_mul'' h1 (mul_lt_mul'' h2' h3' (Nat.zero_le _) (Nat.zero_le _))
    (Nat.zero_le _) (Nat.zero_le _)

private theorem l3pi_F_mono_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) ≤ b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1)) := by
  rcases eq_or_lt_of_le hab with rfl | h
  · exact le_rfl
  · exact (l3pi_F_mono ha h).le

private theorem l3pi_H_mono_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 + 1)) ≤ b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 + 1)) := by
  rcases eq_or_lt_of_le hab with rfl | h
  · exact le_rfl
  · exact (l3pi_H_mono ha h).le

private theorem l3pi_F_lt_H {a : ℕ} (ha : 2 ≤ a) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) < a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 + 1)) := by
  have h0 : 0 < a ^ 3 := pow_pos (by omega) 3
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have hpos : 0 < a ^ 2 - 1 := by omega
  have h3 : a ^ 3 - 1 < a ^ 3 + 1 := by omega
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left h3 hpos) h0

private theorem l3pi_H_lt_F_succ {a : ℕ} (ha : 2 ≤ a) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 + 1)) <
      (a + 1) ^ 3 * (((a + 1) ^ 2 - 1) * ((a + 1) ^ 3 - 1)) := by
  have h0 : 0 < a ^ 3 := pow_pos (by omega) 3
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have hpos : 0 < a ^ 2 - 1 := by omega
  have e3 : (a + 1) ^ 3 = a ^ 3 + 3 * a ^ 2 + 3 * a + 1 := by ring
  have e2 : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
  have hA : a ^ 3 ≤ (a + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hB : a ^ 2 - 1 ≤ (a + 1) ^ 2 - 1 := by omega
  have hC : a ^ 3 + 1 < (a + 1) ^ 3 - 1 := by omega
  have h5 : (a ^ 2 - 1) * (a ^ 3 + 1) < (a ^ 2 - 1) * ((a + 1) ^ 3 - 1) :=
    mul_lt_mul_of_pos_left hC hpos
  have h6 : (a ^ 2 - 1) * ((a + 1) ^ 3 - 1) ≤ ((a + 1) ^ 2 - 1) * ((a + 1) ^ 3 - 1) :=
    Nat.mul_le_mul_right _ hB
  have h7 : a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 + 1)) <
      a ^ 3 * (((a + 1) ^ 2 - 1) * ((a + 1) ^ 3 - 1)) :=
    mul_lt_mul_of_pos_left (lt_of_lt_of_le h5 h6) h0
  exact lt_of_lt_of_le h7 (Nat.mul_le_mul_right _ hA)

private theorem l3pi_F_ne_H {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) ≠ b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 + 1)) := by
  rcases le_or_gt a b with hab | hab
  · exact ((l3pi_F_lt_H ha).trans_le (l3pi_H_mono_le ha hab)).ne
  · exact (lt_of_lt_of_le (l3pi_H_lt_F_succ hb)
      (l3pi_F_mono_le (show 2 ≤ b + 1 by omega) (show b + 1 ≤ a by omega))).ne'

private theorem l3pi_eq_of_order {n a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h1 : n * 3 = a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) ∨
      n * 3 = a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 + 1)))
    (h2 : n * 3 = b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1)) ∨
      n * 3 = b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 + 1))) : a = b := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rcases lt_trichotomy a b with hab | rfl | hab
    · exact absurd (h1.symm.trans h2) (l3pi_F_mono ha hab).ne
    · rfl
    · exact absurd (h2.symm.trans h1) (l3pi_F_mono hb hab).ne
  · exact absurd (h1.symm.trans h2) (l3pi_F_ne_H ha hb)
  · exact absurd (h2.symm.trans h1) (l3pi_F_ne_H hb ha)
  · rcases lt_trichotomy a b with hab | rfl | hab
    · exact absurd (h1.symm.trans h2) (l3pi_H_mono ha hab).ne
    · rfl
    · exact absurd (h2.symm.trans h1) (l3pi_H_mono hb hab).ne

private theorem l3pi_order {X : Type} [Group X] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : Sec4.IsoLThreePi X p f) :
    Nat.card X * 3 = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) ∨
      Nat.card X * 3 = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  have hf0 : f ≠ 0 := by omega
  rcases h with ⟨hmod, ⟨e⟩⟩ | ⟨hmod, ⟨e⟩⟩
  · left
    have hc := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p f)
    rw [GaloisField.card p f hf0] at hc
    have hg : Nat.gcd 3 (p ^ f - 1) = 3 := Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hg] at hc
    rw [Nat.card_congr e.toEquiv]
    exact hc
  · right
    have hc := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd p f hf
    have hg : Nat.gcd 3 (p ^ f + 1) = 3 := Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hg] at hc
    rw [Nat.card_congr e.toEquiv]
    exact hc

theorem isoLThreePi_unique {X : Type} [Group X] {p f p' f' : ℕ} [Fact p.Prime] [Fact p'.Prime]
    (hf : 1 ≤ f) (hf' : 1 ≤ f') (h : Sec4.IsoLThreePi X p f) (h' : Sec4.IsoLThreePi X p' f') :
    p = p' ∧ f = f' := by
  have hp : p.Prime := Fact.out
  have hp' : p'.Prime := Fact.out
  have hq : 2 ≤ p ^ f := (hp.two_le).trans (Nat.le_self_pow (by omega) p)
  have hq' : 2 ≤ p' ^ f' := (hp'.two_le).trans (Nat.le_self_pow (by omega) p')
  have key : p ^ f = p' ^ f' := l3pi_eq_of_order hq hq' (l3pi_order hf h) (l3pi_order hf' h')
  exact Nat.Prime.pow_inj' hp hp' (by omega) (by omega) key

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
