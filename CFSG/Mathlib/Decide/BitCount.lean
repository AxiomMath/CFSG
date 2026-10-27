module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators

public section

namespace CFSG.Decide

@[expose] def bitCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => bitCount n x + if x.testBit n then 1 else 0

theorem card_filter_testBit (n x : ℕ) :
    (Finset.univ.filter fun i : Fin n => x.testBit i = true).card = bitCount n x := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih =>
    rw [bitCount, Finset.card_filter,
      Fin.sum_univ_eq_sum_range (fun i => if x.testBit i = true then 1 else 0) (n + 1),
      Finset.sum_range_succ]
    congr 1
    rw [← ih, Finset.card_filter,
      Fin.sum_univ_eq_sum_range (fun i => if x.testBit i = true then 1 else 0) n]

end CFSG.Decide
