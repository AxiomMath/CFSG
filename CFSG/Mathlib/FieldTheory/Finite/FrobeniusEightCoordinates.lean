module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.FrobeniusEightCoordinates

section CharTwo

variable {L : Type*} [Field L] [CharP L 2]

theorem root_cubic_pow_eight {a : L} (ha : a ^ 3 + a + 1 = 0) : a ^ 8 = a := by
  have h3 : a ^ 3 = a + 1 :=
    CharTwo.add_eq_zero.mp (by simpa [add_assoc] using ha)
  have h4 : a ^ 4 = a ^ 2 + a := by
    calc
      a ^ 4 = a * a ^ 3 := by ring
      _ = a * (a + 1) := by rw [h3]
      _ = a ^ 2 + a := by ring
  have hsq : (a ^ 2 + a) ^ 2 = a ^ 4 + a ^ 2 := by
    rw [CharTwo.add_sq]
    ring
  calc
    a ^ 8 = (a ^ 4) ^ 2 := by ring
    _ = (a ^ 2 + a) ^ 2 := by rw [h4]
    _ = a ^ 4 + a ^ 2 := hsq
    _ = (a ^ 2 + a) + a ^ 2 := by rw [h4]
    _ = a := by
      rw [add_comm (a ^ 2) a]
      exact CharTwo.add_cancel_right a (a ^ 2)

theorem root_cubic_sq_pow_eight {a : L} (ha : a ^ 3 + a + 1 = 0) :
    (a ^ 2) ^ 8 = a ^ 2 := by
  calc
    (a ^ 2) ^ 8 = (a ^ 8) ^ 2 := by ring
    _ = a ^ 2 := by rw [root_cubic_pow_eight ha]

end CharTwo

section Exists

variable {L : Type*} [Field L]

theorem exists_root_cubic [IsAlgClosed L] : ∃ a : L, a ^ 3 + a + 1 = 0 := by
  have hdeg : (Polynomial.X ^ 3 + Polynomial.X + 1 : Polynomial L).degree = 3 := by
    compute_degree!
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 3 + Polynomial.X + 1 : Polynomial L) (by rw [hdeg]; norm_num)
  exact ⟨a, by simpa [Polynomial.IsRoot] using ha⟩

end Exists

section Span

variable {L : Type*} [Field L] [CharP L 2]

theorem exists_frob_eight_span_coeffs_of_root {a : L} (ha : a ^ 3 + a + 1 = 0)
    (u : L) :
    ∃ x0 x1 x2 t0 t1 t2 : L,
      t0 ^ 8 = t0 ∧ t1 ^ 8 = t1 ∧ t2 ^ 8 = t2 ∧
      x0 * t0 + x1 * t1 + x2 * t2 = u ∧
      x0 * t0 ^ 2 + x1 * t1 ^ 2 + x2 * t2 ^ 2 = 0 ∧
      x0 * t0 ^ 4 + x1 * t1 ^ 4 + x2 * t2 ^ 4 = 0 := by
  have h3 : a ^ 3 = a + 1 :=
    CharTwo.add_eq_zero.mp (by simpa [add_assoc] using ha)
  have h4 : a ^ 4 = a ^ 2 + a := by
    calc
      a ^ 4 = a * a ^ 3 := by ring
      _ = a * (a + 1) := by rw [h3]
      _ = a ^ 2 + a := by ring
  have h5 : a ^ 5 = a ^ 2 + a + 1 := by
    calc
      a ^ 5 = a ^ 2 * a ^ 3 := by ring
      _ = a ^ 2 * (a + 1) := by rw [h3]
      _ = a ^ 3 + a ^ 2 := by ring
      _ = (a + 1) + a ^ 2 := by rw [h3]
      _ = a ^ 2 + a + 1 := by ring
  have h6 : a ^ 6 = a ^ 2 + 2 * a + 1 := by
    calc
      a ^ 6 = (a ^ 3) ^ 2 := by ring
      _ = (a + 1) ^ 2 := by rw [h3]
      _ = a ^ 2 + 2 * a + 1 := by ring
  have h8 : a ^ 8 = a := root_cubic_pow_eight ha
  have h8sq : (a ^ 2) ^ 8 = a ^ 2 := root_cubic_sq_pow_eight ha
  have hE1 : u * 1 + (u * a ^ 2) * a + (u * a) * a ^ 2 = u := by
    calc
      u * 1 + (u * a ^ 2) * a + (u * a) * a ^ 2
          = u + u * a ^ 3 + u * a ^ 3 := by ring
      _ = u := CharTwo.add_cancel_right u (u * a ^ 3)
  have hE2 : u * 1 + (u * a ^ 2) * a ^ 2 + (u * a) * (a ^ 2) ^ 2 = 0 := by
    calc
      u * 1 + (u * a ^ 2) * a ^ 2 + (u * a) * (a ^ 2) ^ 2
          = u + u * a ^ 4 + u * a ^ 5 := by ring
      _ = u + u * (a ^ 2 + a) + u * (a ^ 2 + a + 1) := by rw [h4, h5]
      _ = 0 := by
        rw [show u + u * (a ^ 2 + a) + u * (a ^ 2 + a + 1) =
            (u + u * a ^ 2 + u * a) + (u + u * a ^ 2 + u * a) by ring]
        exact CharTwo.add_self_eq_zero _
  have hE3 : u * 1 + (u * a ^ 2) * a ^ 4 + (u * a) * (a ^ 2) ^ 4 = 0 := by
    have h8' : (a ^ 2) ^ 4 = a := by
      calc
        (a ^ 2) ^ 4 = a ^ 8 := by ring
        _ = a := h8
    calc
      u * 1 + (u * a ^ 2) * a ^ 4 + (u * a) * (a ^ 2) ^ 4
          = u + u * a ^ 6 + u * a ^ 2 := by rw [h8']; ring
      _ = u + u * (a ^ 2 + 2 * a + 1) + u * a ^ 2 := by rw [h6]
      _ = 0 := by
        rw [show u + u * (a ^ 2 + 2 * a + 1) + u * a ^ 2 =
            (u + u * a ^ 2 + u * a) + (u + u * a ^ 2 + u * a) by ring]
        exact CharTwo.add_self_eq_zero _
  refine ⟨u, u * a ^ 2, u * a, 1, a, a ^ 2, ?_⟩
  exact ⟨by simp, h8, h8sq, hE1, by simpa only [one_pow] using hE2,
    by simpa only [one_pow] using hE3⟩

theorem exists_frob_eight_span_coeffs [IsAlgClosed L] (u : L) :
    ∃ x0 x1 x2 t0 t1 t2 : L,
      t0 ^ 8 = t0 ∧ t1 ^ 8 = t1 ∧ t2 ^ 8 = t2 ∧
      x0 * t0 + x1 * t1 + x2 * t2 = u ∧
      x0 * t0 ^ 2 + x1 * t1 ^ 2 + x2 * t2 ^ 2 = 0 ∧
      x0 * t0 ^ 4 + x1 * t1 ^ 4 + x2 * t2 ^ 4 = 0 := by
  obtain ⟨a, ha⟩ := exists_root_cubic (L := L)
  exact exists_frob_eight_span_coeffs_of_root ha u

end Span

end CFSG.FrobeniusEightCoordinates
