module

public import CFSG.LinearAlgebra.F2Mat3Cent

public section

namespace CFSG.Quasithin.A94.He42SEK

open CFSG.F2NatMat

@[expose] def noInvComm (a : ℕ) : Bool :=
  allBelow 512 fun b => !eqK 3 (mulK 3 b b) 273 || eqK 3 b 273 ||
    !eqK 3 (mulK 3 a b) (mulK 3 b a)

@[expose] def chk3 (a : ℕ) : Bool :=
  !eqK 3 (mulK 3 (mulK 3 a a) a) 273 || eqK 3 a 273 || noInvComm a

@[expose] def chk7 (a : ℕ) : Bool :=
  !eqK 3 (mulK 3 (mulK 3 (mulK 3 (mulK 3 (mulK 3 (mulK 3 a a) a) a) a) a) a) 273 ||
    eqK 3 a 273 || noInvComm a

theorem chk3_all : allBelow 512 chk3 = true := by decide +kernel

theorem chk7_all : allBelow 512 chk7 = true := by decide +kernel

theorem noInvComm_spec {a : ℕ} (h : noInvComm a = true) (B : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h2 : B * B = 1) (hb1 : B ≠ 1) : dec 3 a * B ≠ B * dec 3 a := by
  obtain ⟨b, hb, rfl⟩ := exists_dec 3 B
  have key := allBelow_spec h b hb
  rw [← dec_mulK, ← dec_273, dec_eq_iff_eqK] at h2
  rw [← dec_273, Ne, dec_eq_iff_eqK] at hb1
  simp only [h2, hb1, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at key
  rw [← dec_mulK, ← dec_mulK, Ne, dec_eq_iff_eqK, key]
  exact Bool.false_ne_true

theorem order3_no_involution :
    ∀ A B : Matrix (Fin 3) (Fin 3) (ZMod 2), A * A * A = 1 → A ≠ 1 → B * B = 1 → B ≠ 1 →
      A * B ≠ B * A := by
  intro A B h3 h1 h2 hb1
  obtain ⟨a, ha, rfl⟩ := exists_dec 3 A
  have key := allBelow_spec chk3_all a ha
  rw [← dec_mulK, ← dec_mulK, ← dec_273, dec_eq_iff_eqK] at h3
  rw [← dec_273, Ne, dec_eq_iff_eqK] at h1
  simp only [chk3, h3, h1, Bool.not_true, Bool.false_or] at key
  exact noInvComm_spec key B h2 hb1

theorem order7_no_involution :
    ∀ A B : Matrix (Fin 3) (Fin 3) (ZMod 2), A * A * A * A * A * A * A = 1 → A ≠ 1 →
      B * B = 1 → B ≠ 1 → A * B ≠ B * A := by
  intro A B h7 h1 h2 hb1
  obtain ⟨a, ha, rfl⟩ := exists_dec 3 A
  have key := allBelow_spec chk7_all a ha
  rw [← dec_mulK, ← dec_mulK, ← dec_mulK, ← dec_mulK, ← dec_mulK, ← dec_mulK, ← dec_273,
    dec_eq_iff_eqK] at h7
  rw [← dec_273, Ne, dec_eq_iff_eqK] at h1
  simp only [chk7, h7, h1, Bool.not_true, Bool.false_or] at key
  exact noInvComm_spec key B h2 hb1

end CFSG.Quasithin.A94.He42SEK
