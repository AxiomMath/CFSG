module

public import CFSG.Sporadic.Co2Smith.GlDataRoot
public import CFSG.Sporadic.Co2Smith.GlDataRootCheck
public import CFSG.Sporadic.Co2Smith.GlDataElts

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glRoot_parts :
    Native.glRootParOK = true ∧ Native.glRootCommOK = true ∧ Native.glChartOK = true ∧
      Native.glUOK = true ∧ Native.glFrameOK = true := by
  have h := glRoot_check
  simp only [Native.glRootOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem eq_of_val_rows {u v : K} {X Y : Array ℕ} (hu : u.val.val = rowsMatrix 22 X)
    (hv : v.val.val = rowsMatrix 22 Y) (h : X = Y) : u = v :=
  eq_of_rows hu hv h

theorem xRootK_mul {r s t : ℕ}
    (hr : r < 12) (hs : s ∈ [1, 2, 3]) (ht : t ∈ [1, 2, 3]) :
    xRootK r s * xRootK r t = xRootK r (s ^^^ t) := by
  have h := glRoot_parts.1
  simp only [Native.glRootParOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq] at h
  refine eq_of_val_rows ?_ (xRootK_val _ _) ((h r hr t ht).1.1 s hs)
  rw [val_val_mul, xRootK_val, xRootK_val, rowsMatrix_mulRows]

theorem xRootK_α3 {r t : ℕ}
    (hr : r < 12) (ht : t ∈ [1, 2, 3]) :
    α3K * α3K * xRootK r t * α3K = xRootK r (Native.f4mul Native.glRootChar[r]! t) := by
  have h := glRoot_parts.1
  simp only [Native.glRootParOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq] at h
  refine eq_of_val_rows ?_ (xRootK_val _ _) (h r hr t ht).1.2
  rw [val_val_mul, val_val_mul, val_val_mul, α3K_val, xRootK_val, rowsMatrix_mulRows,
    rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem glChart_spec :
    (∀ r < 12, ∀ k < 6, Native.glChartCoord r k < 0 ∨
      ∀ t ∈ [1, 2, 3], Native.commRows (Native.glRootRows r t) (Native.glLongRows k) = true) ∧
    ∀ k < 6, mulRows 22 (Native.glFrameConjRows k) (Native.glLongRows k) =
      mulRows 22 Native.glZ (Native.glFrameConjRows k) := by
  have h := glRoot_parts.2.2.1
  simp only [Native.glChartOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem xRootK_comm_long
    {r k t : ℕ} (hr : r < 12) (hk : k < 6) (hc : 0 ≤ Native.glChartCoord r k)
    (ht : t ∈ [1, 2, 3]) : xRootK r t * xLongK k = xLongK k * xRootK r t := by
  rcases glChart_spec.1 r hr k hk with h | h
  · exact absurd hc (not_le.2 h)
  · exact comm_of_commRows (xRootK_val _ _) (xLongK_val _) (h t ht)

theorem frameConjK_conj {k : ℕ}
    (hk : k < 6) : frameConjK k * xLongK k = z0 * frameConjK k :=
  eq_of_val_rows (by rw [val_val_mul, frameConjK_val, xLongK_val, rowsMatrix_mulRows])
    (by rw [val_val_mul, z0_val', frameConjK_val, rowsMatrix_mulRows]) (glChart_spec.2 k hk)

theorem glFrame_spec :
    (∀ k < 6, mulRows 22 (Native.glLongRows k) (Native.glLongRows k) = idRows 22) ∧
    (∀ i < 3, powRows 22 (mulRows 22 (Native.glLongRows i) (Native.glLongRows (i + 3))) 3 =
      idRows 22) ∧
    (∀ k < 6, ∀ l < 6, k % 3 = l % 3 ∨
      Native.commRows (Native.glLongRows k) (Native.glLongRows l) = true) ∧
    mulRows 22 Native.glD0h Native.glD0h = idRows 22 ∧
    mulRows 22 Native.glD1h Native.glD1h = idRows 22 ∧
    powRows 22 (mulRows 22 Native.glD0h Native.glD1h) 3 = idRows 22 ∧
    Native.commRows Native.glD0h Native.glZ = true ∧
    Native.commRows Native.glD0h Native.glX61 = true ∧
    Native.commRows Native.glD1h Native.glX34 = true ∧
    Native.commRows Native.glD1h Native.glX43 = true := by
  have h := glRoot_parts.2.2.2.2
  simp only [Native.glFrameOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem xLongK_mul_self {k : ℕ}
    (hk : k < 6) : xLongK k * xLongK k = 1 := by
  apply eq_of_val_eq
  rw [val_val_mul, xLongK_val, ← rowsMatrix_mulRows, glFrame_spec.1 k hk, rowsMatrix_idRows]
  rfl

theorem xLongK_comm {k l : ℕ}
    (hk : k < 6) (hl : l < 6) (h : k % 3 ≠ l % 3) : xLongK k * xLongK l = xLongK l * xLongK k := by
  rcases glFrame_spec.2.2.1 k hk l hl with h' | h'
  · exact absurd h' h
  · exact comm_of_commRows (xLongK_val _) (xLongK_val _) h'

theorem δ0hK_mul_self :
    δ0hK * δ0hK = 1 := by
  apply eq_of_val_eq
  rw [val_val_mul, δ0hK_val, ← rowsMatrix_mulRows, glFrame_spec.2.2.2.1, rowsMatrix_idRows]
  rfl

theorem δ1hK_mul_self :
    δ1hK * δ1hK = 1 := by
  apply eq_of_val_eq
  rw [val_val_mul, δ1hK_val, ← rowsMatrix_mulRows, glFrame_spec.2.2.2.2.1, rowsMatrix_idRows]
  rfl

theorem δhK_comm :
    δ0hK * x16K = x16K * δ0hK ∧ δ0hK * x61K = x61K * δ0hK ∧ δ1hK * x34K = x34K * δ1hK ∧
      δ1hK * x43K = x43K * δ1hK := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4⟩ := glFrame_spec
  exact ⟨comm_of_commRows δ0hK_val x16K_val h1, comm_of_commRows δ0hK_val x61K_val h2,
    comm_of_commRows δ1hK_val x34K_val h3, comm_of_commRows δ1hK_val x43K_val h4⟩

end CFSG.Sporadic.Co2Smith
