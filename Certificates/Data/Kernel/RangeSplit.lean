module

public import Init

public section

namespace CFSG.KC.RangeSplit

theorem andT {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem all_range'_split {f : Nat → Bool} {a m k : Nat} (h1 : (List.range' a m).all f = true)
    (h2 : (List.range' (a + m) k).all f = true) : (List.range' a (m + k)).all f = true := by
  rw [← List.range'_append_1, List.all_append, h1, h2]
  rfl

theorem all_cut {α : Type} {f : α → Bool} (l : List α) (c : Nat) (h1 : (l.take c).all f = true)
    (h2 : (l.drop c).all f = true) : l.all f = true := by
  rw [← List.take_append_drop c l, List.all_append, h1, h2]
  rfl

end CFSG.KC.RangeSplit

end
