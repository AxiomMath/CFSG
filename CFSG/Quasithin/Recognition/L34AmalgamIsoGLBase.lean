
module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoGLInputs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace CFSG.Quasithin.L34Amalgam

theorem bxor_comm : ∀ x y : Fin 16, bxor x y = bxor y x := by decide

theorem bxor_assoc : ∀ x y z : Fin 16, bxor (bxor x y) z = bxor x (bxor y z) := by decide

theorem bxor_left_comm (x y z : Fin 16) : bxor x (bxor y z) = bxor y (bxor x z) := by
  rw [← bxor_assoc, bxor_comm x y, bxor_assoc]

theorem bxor_zero : ∀ x : Fin 16, bxor x 0 = x := by decide

theorem zero_bxor (x : Fin 16) : bxor 0 x = x := by rw [bxor_comm, bxor_zero]

theorem bxor_self : ∀ x : Fin 16, bxor x x = 0 := by decide

theorem bit_bxor : ∀ (i : Fin 4) (x y : Fin 16), bit i (bxor x y) = xor (bit i x) (bit i y) := by
  decide

theorem sel_xor (a b : Bool) (m : Fin 16) : sel (xor a b) m = bxor (sel a m) (sel b m) := by
  cases a <;> cases b <;> simp [sel, bxor_zero, zero_bxor, bxor_self]

theorem lin_bxor (m : Fin 4 → Fin 16) (x y : Fin 16) :
    lin m (bxor x y) = bxor (lin m x) (lin m y) := by
  simp only [lin, bit_bxor, sel_xor]
  simp only [bxor_assoc, bxor_left_comm]

theorem lin_zero (m : Fin 4 → Fin 16) : lin m 0 = 0 := by
  have h := lin_bxor m 0 0
  rw [bxor_self] at h
  have h2 : bxor (lin m 0) (lin m 0) = 0 := bxor_self _
  rw [← h] at h2
  exact h2

theorem lin_sel (T : Fin 4 → Fin 16) (b : Bool) (m : Fin 16) :
    lin T (sel b m) = sel b (lin T m) := by
  cases b
  · simp [sel, lin_zero]
  · simp [sel]

theorem lin_comp (T M : Fin 4 → Fin 16) (x : Fin 16) :
    lin T (lin M x) = lin (fun i => lin T (M i)) x := by
  show lin T (bxor (bxor (sel (bit 0 x) (M 0)) (sel (bit 1 x) (M 1)))
    (bxor (sel (bit 2 x) (M 2)) (sel (bit 3 x) (M 3)))) = _
  rw [lin_bxor, lin_bxor, lin_bxor, lin_sel, lin_sel, lin_sel, lin_sel]
  rfl

theorem eq_lin_basis : ∀ x : Fin 16, lin ![1, 2, 4, 8] x = x := by decide

@[expose] def toCode (m : Fin 4 → Fin 16) : ℕ := m 0 + 16 * m 1 + 256 * m 2 + 4096 * m 3

theorem toCode_lt (m : Fin 4 → Fin 16) : toCode m < 65536 := by
  unfold toCode; omega

theorem ofCode_toCode (m : Fin 4 → Fin 16) : ofCode (toCode m) = m := by
  funext i
  fin_cases i <;> simp only [ofCode, toCode] <;> apply Fin.ext <;> simp <;> omega

theorem exists_of_checkPair {u v : Fin 4 → Fin 16} (h : checkPair u v = true)
    (h5 : ∀ i, (lin u ∘ lin v)^[5] (basisVec i) = basisVec i) :
    ∃ w : Fin 16, (∀ x, x ≠ 0 → lin (conjMap u v w) x ≠ 0) ∧
      (∀ i, lin (conjMap u v w) (refA i) = lin u (conjMap u v w i)) ∧
      ∀ i, lin (conjMap u v w) (refB i) = lin v (conjMap u v w i) := by
  unfold checkPair at h
  rw [ite_eq_left (by simpa using h5)] at h
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨w, ⟨hinj, hA⟩, hB⟩ := h
  refine ⟨w, fun x hx => ?_, fun i => hA i trivial, fun i => hB i trivial⟩
  rcases hinj x trivial with h0 | h0
  · exact absurd h0 hx
  · exact h0

end CFSG.Quasithin.L34Amalgam
