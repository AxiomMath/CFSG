module

public import Certificates.Data.CFSGNative.PairSchreier.Core
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Schreier.PairNative

theorem foldl_add_shift {α : Type*} (g : α → ℕ) :
    ∀ (l : List α) (a : ℕ), l.foldl (fun c t => c + g t) a = a + l.foldl (fun c t => c + g t) 0
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons]
    rw [foldl_add_shift g l (a + g x), foldl_add_shift g l (0 + g x)]
    omega

theorem countW_split (f : List (Array ℕ) → Bool) (B : Array (Array ℕ))
    (Bs : List (Array (Array ℕ))) (k : ℕ) :
    countW f (B :: Bs) [] =
      countW f (B.extract 0 k :: Bs) [] + countW f (B.extract k B.size :: Bs) [] := by
  rw [countW.eq_2, countW.eq_2, countW.eq_2]
  have hB : B.extract 0 k ++ B.extract k B.size = B := by
    rw [Array.extract_append_extract, Nat.zero_min,
      Array.extract_eq_self_of_le (Nat.le_max_right _ _)]
  have h := congrArg (Array.foldl (fun c t => c + countW f Bs [t]) 0) hB
  rw [← h, Array.foldl_append, ← Array.foldl_toList (xs := B.extract k B.size),
    foldl_add_shift, Array.foldl_toList]

end CFSG.Sporadic.SmallOddCore
