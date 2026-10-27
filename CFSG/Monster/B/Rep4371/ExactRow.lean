module

public import CFSG.Monster.B.Rep4371.Raw

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Griess

theorem rawModel_valid (k : ℕ) : ∀ e ∈ Model.rawModel k, KeyValid e.1 := by
  intro e he
  unfold Model.rawModel at he
  split_ifs at he with h0 h22 h66 h1 h1090 h2322 <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he <;>
    (try rcases he with rfl | rfl) <;>
    simp only [KeyValid, Model.Key.A, Model.Key.X, Model.Key.W, Model.minusKey, Model.plusKey,
      Model.oddKey, Model.octKey] <;> intro h <;> omega

theorem interp_rowModel (row : Array (ℕ × ℤ)) :
    interp 512 (Model.rowModel row) = (row.toList.map fun e => ((e.2 : ℚ) / 8) • Rraw e.1).sum := by
  rw [Model.rowModel]
  induction row.toList with
  | nil => simp
  | cons e l ih =>
    rw [List.flatMap_cons, interp_append, ih, List.map_cons, List.sum_cons, Rraw_eq_interp]
    congr 1
    have h := interp_map_mul e.2 8 (Model.rawModel e.1)
    norm_num at h ⊢
    exact h

theorem act_Rraw_of_rowOK (g : Model.Key → List (Model.Key × ℤ)) (f : SpaceB →ₗ[ℚ] SpaceB)
    (hf : ∀ κ, KeyValid κ → f (keyVec κ) = interp 64 (g κ))
    {row : Array (ℕ × ℤ)} {k : ℕ} (hrow : Model.rowOK g row k = true) :
    f (Rraw k) = (row.toList.map fun e => ((e.2 : ℚ) / 8) • Rraw e.1).sum := by
  rw [Rraw_eq_interp, interp_actVec g f 64 _ fun e he => hf e.1 (rawModel_valid k e he),
    ← interp_rowModel]
  have h := eqModel_sound (by norm_num) (by norm_num) hrow
  norm_num at h ⊢
  exact h

@[expose] def rowNum (l : List (ℕ × ℤ)) (u : ℕ) : ℤ := (l.map fun e => if e.1 = u then e.2 else 0).sum

theorem foldl_eq_rowNum (l : List (ℕ × ℤ)) (u : ℕ) (s : ℤ) :
    l.foldl (fun s e => if e.1 = u then s + e.2 else s) s = s + rowNum l u := by
  induction l generalizing s with
  | nil => simp [rowNum]
  | cons e l ih =>
    simp only [List.foldl_cons, ih, rowNum, List.map_cons, List.sum_cons]
    split_ifs <;> ring

theorem sum_row_eq_sum_fin {n : ℕ} (R : ℕ → SpaceB) (l : List (ℕ × ℤ))
    (hl : ∀ e ∈ l, e.1 < n) :
    (l.map fun e => ((e.2 : ℚ) / 8) • R e.1).sum =
      ∑ u : Fin n, (((rowNum l u : ℤ) : ℚ) / 8) • R u := by
  induction l with
  | nil => simp [rowNum]
  | cons e l ih =>
    rw [List.map_cons, List.sum_cons, ih fun f hf => hl f (List.mem_cons_of_mem _ hf)]
    have he : e.1 < n := hl e List.mem_cons_self
    simp only [rowNum, List.map_cons, List.sum_cons, Int.cast_add, add_div, add_smul,
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨e.1, he⟩]
    · rw [ite_eq_left rfl]
    · intro u _ hu
      rw [ite_eq_right fun h => hu (Fin.ext h.symm), Int.cast_zero, zero_div, zero_smul]
    · simp

end CFSG.Monster.B.Rep4371
