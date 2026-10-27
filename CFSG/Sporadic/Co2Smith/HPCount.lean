module

public import CFSG.Sporadic.Co2Smith.S0Enum

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose, irreducible] def cT : Array (Array (Array ℕ)) := Native.tArrN seedRowsArr

theorem cT_eq : cT = Native.tArrN seedRowsArr := by unfold cT; rfl

theorem sElt_val'
    (n : ℕ) : (sElt n).val.val = rowsMatrix 22 (Native.sRowsN cT n) := by
  rw [cT_eq]
  exact sElt_val n

theorem sum_filter_range (N : ℕ) (g : ℕ → Bool) (c : ℕ → ℕ) :
    (((List.range N).filter g).map c).sum = ∑ n ∈ Finset.range N, if g n then c n else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    congr 1
    by_cases h : g N <;> simp [h]

theorem length_filter_range (m : ℕ) (q : ℕ → Bool) :
    ((List.range m).filter q).length = ((Finset.range m).filter fun e => q e = true).card := by
  rw [← List.countP_eq_length_filter, Finset.card_filter, ← sum_filter_range m q (fun _ => 1)]
  simp [List.countP_eq_length_filter]

end CFSG.Sporadic.Co2Smith
