module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBTwist

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

@[expose] def tens {j n : ℕ} (a : Fin n → ZMod 2) (x : Fin j → ZMod 2) : Fin j → Fin n → ZMod 2 :=
  fun i => x i • a

theorem tens_apply {j n : ℕ} (a : Fin n → ZMod 2) (x : Fin j → ZMod 2) (i : Fin j) :
    tens a x i = x i • a := rfl

theorem tens_add_left {j n : ℕ} (a b : Fin n → ZMod 2) (x : Fin j → ZMod 2) :
    tens (a + b) x = tens a x + tens b x := by
  funext i
  simp [tens, smul_add]

theorem tens_add_right {j n : ℕ} (a : Fin n → ZMod 2) (x y : Fin j → ZMod 2) :
    tens a (x + y) = tens a x + tens a y := by
  funext i
  simp [tens, add_smul]

theorem tens_zero_left {j n : ℕ} (x : Fin j → ZMod 2) : tens (0 : Fin n → ZMod 2) x = 0 := by
  funext i
  simp [tens]

theorem tens_zero_right {j n : ℕ} (a : Fin n → ZMod 2) : tens a (0 : Fin j → ZMod 2) = 0 := by
  funext i
  simp [tens]

theorem tens_eq_zero_iff {j n : ℕ} (a : Fin n → ZMod 2) (x : Fin j → ZMod 2) :
    tens a x = 0 ↔ a = 0 ∨ x = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact ha (funext hcon)
      funext i
      have hik : x i * a k = 0 := by
        have h2 := congrFun (congrFun h i) k
        simpa [tens] using h2
      exact (mul_eq_zero.mp hik).resolve_right hk
  · rintro (rfl | rfl)
    · exact tens_zero_left x
    · exact tens_zero_right a

theorem tens_mulVec {j n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (a : Fin n → ZMod 2)
    (x : Fin j → ZMod 2) :
    (fun i => M.mulVec (tens a x i)) = tens (M.mulVec a) x := by
  funext i
  simp only [tens, Matrix.mulVec_smul]

theorem sum_tens {j n : ℕ} (t : Fin j → Fin n → ZMod 2) :
    t = ∑ b : Fin n, tens (Pi.single b 1) (fun i => t i b) := by
  funext i c
  simp [tens, Finset.sum_apply, Pi.single_apply]

theorem tens_apply_apply {j n : ℕ} (a : Fin n → ZMod 2) (x : Fin j → ZMod 2) (i : Fin j)
    (b : Fin n) : tens a x i b = x i * a b := by
  simp [tens, smul_eq_mul]

end CFSG.Quasithin.H13.Ch4.NSB
