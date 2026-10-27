module

public import CFSG.Quasithin.EmptyFaithful.R3c6Fam
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.Quasithin.R3c6

open CFSG.Open (ordG2 ordTrialityD4 ordTwistedF4 ordTits)
open CFSG.Quasithin CFSG.Timmesfeld.Orders CFSG.Assembly.LowTwoRank CFSG.Blueprint

variable {X : Type} [Group X]

section Exc

theorem notOdd_g2_two {f : ℕ} (hf : 1 ≤ f) (h : ChevalleyExceptionalModel X .G2 2 f) :
    ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = ordG2 (2 ^ f) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  rw [ordG2_eq] at hN
  have h6 := odd_pow_sub_one hf (a := 6) (by norm_num)
  have h2 := odd_pow_sub_one hf (a := 2) (by norm_num)
  have hQ : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  refine notOddOrder_of_two_part (g := 1) odd_one (h6.mul h2) (a := f * 6) (b := f * 14)
    (by rw [mul_one, hN]) ?_ (by omega)
  have := two_pow_mul_lt (f := f) (a := 6) (k := 8) (r := ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) (by
    calc ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 6 * (2 ^ f) ^ 2 :=
          Nat.mul_lt_mul'' (sub_one_lt_pow _ _ hQ) (sub_one_lt_pow _ _ hQ)
      _ = (2 ^ f) ^ 8 := by ring)
  simpa using this


theorem notOdd_3d4_two {f : ℕ} (hf : 1 ≤ f) (h : ChevalleyExceptionalModel X .trialityD4 2 f) :
    ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = ordTrialityD4 (2 ^ f) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  have hm : ordTrialityD4 (2 ^ f) = 2 ^ (f * 12) *
      (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
    rw [ordTrialityD4, pow_mul]; ring
  rw [hm] at hN
  have hE : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  have h1 : Odd ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) :=
    (((Nat.even_pow' (by norm_num)).2 hE).add ((Nat.even_pow' (by norm_num)).2 hE)).add_one
  have h6 := odd_pow_sub_one hf (a := 6) (by norm_num)
  have h2 := odd_pow_sub_one hf (a := 2) (by norm_num)
  have hQ2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQ : 1 ≤ 2 ^ f := by omega
  refine notOddOrder_of_two_part (g := 1) odd_one (h1.mul (h6.mul h2)) (a := f * 12) (b := f * 29)
    (by rw [mul_one, hN]) ?_ (by omega)
  have hlt : (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 < (2 ^ f) ^ 9 := by
    set Q := 2 ^ f with hQdef
    have hQ4 : 16 ≤ Q ^ 4 :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ Q ^ 4 := Nat.pow_le_pow_left hQ2 4
    have h8 : Q ^ 8 = Q ^ 4 * Q ^ 4 := by ring
    have h9 : Q ^ 9 = Q * Q ^ 8 := by ring
    nlinarith
  have := two_pow_mul_lt (f := f) (a := 12) (k := 17)
    (r := ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) (by
    calc ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))
        < (2 ^ f) ^ 9 * ((2 ^ f) ^ 6 * (2 ^ f) ^ 2) :=
          Nat.mul_lt_mul'' hlt (Nat.mul_lt_mul'' (sub_one_lt_pow _ _ hQ) (sub_one_lt_pow _ _ hQ))
      _ = (2 ^ f) ^ 17 := by ring)
  simpa using this

theorem notOdd_2f4_two {f : ℕ} (hf : 1 ≤ f) (h : ReeTitsModel X .twistedF4 2 f) :
    ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = ordTwistedF4 (2 ^ f) :=
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h
  have hm : ordTwistedF4 (2 ^ f) = 2 ^ (f * 12) * (((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) *
      (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) := by
    rw [ordTwistedF4, pow_mul]; ring
  rw [hm] at hN
  have h6 := odd_pow_add_one hf (a := 6) (by norm_num)
  have h4 := odd_pow_sub_one hf (a := 4) (by norm_num)
  have h3 := odd_pow_add_one hf (a := 3) (by norm_num)
  have h1 := odd_two_pow_sub_one hf
  have hQ2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQ : 1 ≤ 2 ^ f := by omega
  refine notOddOrder_of_two_part (g := 1) odd_one (h6.mul (h4.mul (h3.mul h1))) (a := f * 12)
    (b := f * 28) (by rw [mul_one, hN]) ?_ (by omega)
  have e1 : (2 ^ f) ^ 6 + 1 < (2 ^ f) ^ 7 := pow_add_one_lt _ 6 hQ2 (by norm_num)
  have e3 : (2 ^ f) ^ 3 + 1 < (2 ^ f) ^ 4 := pow_add_one_lt _ 3 hQ2 (by norm_num)
  have e4 : (2 ^ f) ^ 4 - 1 < (2 ^ f) ^ 4 := sub_one_lt_pow _ _ hQ
  have e0 : 2 ^ f - 1 < 2 ^ f := Nat.sub_lt hQ one_pos
  have := two_pow_mul_lt (f := f) (a := 12) (k := 16)
    (r := ((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) * (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) (by
    calc ((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) * (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))
        < (2 ^ f) ^ 7 * ((2 ^ f) ^ 4 * ((2 ^ f) ^ 4 * 2 ^ f)) :=
          Nat.mul_lt_mul'' e1 (Nat.mul_lt_mul'' e4 (Nat.mul_lt_mul'' e3 e0))
      _ = (2 ^ f) ^ 16 := by ring)
  simpa using this

end Exc

section Tits


theorem notOdd_tits {f : ℕ} (h : ReeTitsModel X .Tits 2 f) : ¬ IsOddOrder (Nat.card X) := by
  have hN : Nat.card X = ordTits := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits h
  rw [ordTits_eq] at hN
  exact notOddOrder_of_two_part (g := 1) odd_one (by decide : Odd 8775) (a := 11) (b := 25)
    (by rw [mul_one, hN]) (by norm_num) (by norm_num)

end Tits

end CFSG.Quasithin.R3c6
