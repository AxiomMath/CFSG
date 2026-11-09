module

public import Certificates.Data.Kernel.ChengHeldSec2K

public section

namespace CFSG.KC.ChengHeldS2

variable (N : ℕ) (m : ℕ → ℕ → ℕ) (inv : ℕ → ℕ)

@[expose] def pfRowC (a1 a2 : ℕ → ℕ) (s1 : ℕ) : Bool :=
  decide ((fixSet1K N m inv a1 s1).length < 8) ||
    (List.range N).all fun s2 => pairCaseK m inv a2 (fixSet1K N m inv a1 s1) s2

@[expose] def pfBlkC (a1 a2 : ℕ → ℕ) (lo len : ℕ) : Bool :=
  (List.range len).all fun t => pfRowC N m inv a1 a2 (lo + t)

theorem pairCaseK_of_short {a2 : ℕ → ℕ} {F1 : List ℕ} (h : F1.length < 8) (s2 : ℕ) :
    pairCaseK m inv a2 F1 s2 = true := by
  unfold pairCaseK
  have hl := List.length_filter_le (fun x => a2 (cjK m inv x s2) == x) F1
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl (Nat.lt_of_le_of_lt hl h)

theorem row_of_pfRowC {a1 a2 : ℕ → ℕ} {s1 : ℕ} (h : pfRowC N m inv a1 a2 s1 = true) :
    ((List.range N).all fun s2 => pairCaseK m inv a2 (fixSet1K N m inv a1 s1) s2) = true := by
  unfold pfRowC at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · simp only [List.all_eq_true]
    exact fun s2 _ => pairCaseK_of_short m inv (of_decide_eq_true h) s2
  · exact h

theorem pairFixK_of_blocks {a1 a2 : ℕ → ℕ} (B k : ℕ) (hN : N = k * B)
    (h : ∀ j < k, pfBlkC N m inv a1 a2 (j * B) B = true) : pairFixK N m inv a1 a2 = true := by
  unfold pairFixK
  rw [List.all_eq_true]
  intro s1 hs1
  rw [List.mem_range] at hs1
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.mul_zero] at hN; omega
    · exact h0
  have hj : s1 / B < k := (Nat.div_lt_iff_lt_mul hB).2 (by rw [← hN]; exact hs1)
  have hb := h (s1 / B) hj
  unfold pfBlkC at hb
  simp only [List.all_eq_true] at hb
  have hr := hb (s1 % B) (List.mem_range.2 (Nat.mod_lt _ hB))
  have e : s1 / B * B + s1 % B = s1 := by rw [Nat.mul_comm]; exact Nat.div_add_mod s1 B
  rw [e] at hr
  exact row_of_pfRowC N m inv hr

end CFSG.KC.ChengHeldS2

end
