module

public import Init

public section

namespace CFSG.KC.G23F48

@[expose] def reachOK (n k p : Nat) (G : Array (Array Nat)) (T : List (Nat × Nat × Nat)) : Bool :=
  (T.getD 0 (0, 0, 0)).1 == p && decide (p < n) &&
    (List.range T.length).all fun i =>
      decide ((T.getD i (0, 0, 0)).1 < n) &&
        (i == 0 || decide ((T.getD i (0, 0, 0)).2.1 < i) && decide ((T.getD i (0, 0, 0)).2.2 < k) &&
          (G[(T.getD i (0, 0, 0)).2.2]!)[(T.getD (T.getD i (0, 0, 0)).2.1 (0, 0, 0)).1]! ==
            (T.getD i (0, 0, 0)).1)

end CFSG.KC.G23F48

end
