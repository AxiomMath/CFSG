module

public import CFSG.RankThree.GF2n.Parrott.PSp43Pack45

public section

namespace CFSG.RankThree.GF2n.Parrott.FusionE16.Pack

open Equiv CFSG.KC.Enum CFSG.KS.PK CFSG.Permutation.FinPack64
  CFSG.RankThree.GF2n.Parrott.Pack45
open CFSG.KS.PCnt (pkw)

@[expose] noncomputable def ifK (c : Bool) (t e : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) e t c

@[expose] noncomputable def cjK (k : ℕ) : ℕ :=
  ifK (Nat.beq k 10) (mulW 45 (mulW 45 (mulW 45 cS1 cS1) cS2) cS2) <|
  ifK (Nat.beq k 26) (mulW 45 (mulW 45 (mulW 45 (mulW 45 cB1 cS1) cS1) cS2) cS2) <|
  ifK (Nat.beq k 6) (mulW 45 cS1 cS1) <|
  ifK (Nat.beq k 22) (mulW 45 (mulW 45 cB1 cS1) cS1) <|
  ifK (Nat.beq k 14) (mulW 45 (mulW 45 (mulW 45 cB1 cS1) cS1) cS2) <|
  ifK (Nat.beq k 30) (mulW 45 (mulW 45 cS1 cS1) cS2) <|
  ifK (Nat.beq k 9) (mulW 45 cS2 cS2) <|
  ifK (Nat.beq k 25) (mulW 45 (mulW 45 cB1 cS2) cS2) <|
  ifK (Nat.beq k 21) cB1 <|
  ifK (Nat.beq k 13) (mulW 45 cB1 cS2) <|
  ifK (Nat.beq k 29) cS2 <|
  ifK (Nat.beq k 11) (mulW 45 (mulW 45 (mulW 45 cB1 cS1) cS2) cS2) <|
  ifK (Nat.beq k 27) (mulW 45 (mulW 45 cS1 cS2) cS2) <|
  ifK (Nat.beq k 7) (mulW 45 cB1 cS1) <|
  ifK (Nat.beq k 23) cS1 <|
  ifK (Nat.beq k 15) (mulW 45 cS1 cS2) <|
  ifK (Nat.beq k 31) (mulW 45 (mulW 45 cB1 cS1) cS2) cOne

private theorem beq_false {k j : ℕ} (h : k = j → False) : Nat.beq k j = false := by
  cases e : Nat.beq k j
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem cjK_other (k : ℕ) (h10 : k = 10 → False) (h26 : k = 26 → False) (h6 : k = 6 → False)
    (h22 : k = 22 → False) (h14 : k = 14 → False) (h30 : k = 30 → False) (h9 : k = 9 → False)
    (h25 : k = 25 → False) (h21 : k = 21 → False) (h13 : k = 13 → False)
    (h29 : k = 29 → False) (h11 : k = 11 → False) (h27 : k = 27 → False) (h7 : k = 7 → False)
    (h23 : k = 23 → False) (h15 : k = 15 → False) (h31 : k = 31 → False) : cjK k = cOne := by
  rw [cjK, beq_false h10, beq_false h26, beq_false h6, beq_false h22, beq_false h14,
    beq_false h30, beq_false h9, beq_false h25, beq_false h21, beq_false h13, beq_false h29,
    beq_false h11, beq_false h27, beq_false h7, beq_false h23, beq_false h15, beq_false h31]
  rfl

@[expose] noncomputable def chkCT : Bool :=
  all2 fun b0 => all2 fun b1 => all2 fun b2 => all2 fun b3 => all2 fun b4 =>
    strictB (q0K b0 b1 b2 b3 b4) fun Q =>
      Bool.rec (motive := fun _ => Bool) true
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (strictB (cjK (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4)) fun C =>
              Nat.beq (mulW 45 C Q) (mulW 45 (mulW 45 cA1 cA2) C))
            true (Nat.beq Q cOne))
          true (Nat.beq Q cT))
        (Nat.beq (mulW 45 Q Q) cOne)

theorem chkCT_eq : chkCT = true := by decide +kernel

theorem conj_table_sound (p : Fin 5 → Fin 2) {c : Perm (Fin 45)}
    (hc : pkw 6 c = cjK ((p 0 : ℕ) + 2 * (p 1 : ℕ) + 4 * (p 2 : ℕ) + 8 * (p 3 : ℕ) + 16 * (p 4 : ℕ)))
    (h2 : q0w p * q0w p = 1) (ht : q0w p ≠ t) (h1 : q0w p ≠ 1) :
    c * q0w p * c⁻¹ = alpha1 * alpha2 := by
  have h := all2_spec (all2_spec (all2_spec (all2_spec (all2_spec chkCT_eq (p 0).isLt)
    (p 1).isLt) (p 2).isLt) (p 3).isLt) (p 4).isLt
  simp only [strictB_eq] at h
  have hq := pk_q0 p
  have hsq : mulW 45 (q0K (p 0) (p 1) (p 2) (p 3) (p 4)) (q0K (p 0) (p 1) (p 2) (p 3) (p 4)) =
      cOne := by
    rw [← pk_mul h45 hq hq, h2, pk_one]
  rw [hsq, Nat.beq_refl, beq_false_of_ne h45 hq pk_t ht, beq_false_of_ne h45 hq pk_one h1] at h
  have h3 := brec_false (b := true) (brec_false (b := true) (brec_true (a := true) h))
  exact conj_of h45 hc hq (pk_mul h45 pk_a1 pk_a2) (Nat.eq_of_beq_eq_true h3)

end CFSG.RankThree.GF2n.Parrott.FusionE16.Pack
