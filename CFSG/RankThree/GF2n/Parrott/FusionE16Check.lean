module

public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.RankThree.GF2n.Parrott.FusionE16

@[expose] def vmul (v r0 r1 r2 r3 : ℕ) : ℕ :=
  (if v.testBit 0 then r0 else 0) ^^^ (if v.testBit 1 then r1 else 0) ^^^
  (if v.testBit 2 then r2 else 0) ^^^ (if v.testBit 3 then r3 else 0)

@[expose] def tab (r0 r1 r2 r3 : ℕ) : List ℕ := (List.range 16).map fun v => vmul v r0 r1 r2 r3

@[expose] def comp (t u : List ℕ) : List ℕ := (List.range 16).map fun v => t.getD (u.getD v 0) 0

@[expose] def idTab : List ℕ := List.range 16

@[expose] def A4tabs : List (List ℕ) :=
  [tab 1 4 6 8, tab 1 4 7 13, tab 1 2 4 8, tab 1 2 5 11, tab 1 6 2 8, tab 1 6 3 15, tab 1 5 6 15,
   tab 1 5 7 11, tab 1 3 4 13, tab 1 3 5 15, tab 1 7 2 11, tab 1 7 3 13]

@[expose] def pairs16 : List (List ℕ × List ℕ) :=
  [(tab 1 4 6 8, tab 1 5 6 15), (tab 1 2 4 8, tab 1 3 4 13), (tab 1 6 2 8, tab 1 7 2 11),
   (tab 1 4 7 13, tab 1 5 7 11), (tab 1 2 5 11, tab 1 3 5 15), (tab 1 6 3 15, tab 1 7 3 13),
   (tab 1 4 6 8, tab 1 5 7 11), (tab 1 4 7 13, tab 1 5 6 15), (tab 1 2 4 8, tab 1 3 5 15),
   (tab 1 2 5 11, tab 1 3 4 13), (tab 1 4 6 8, tab 1 2 4 8), (tab 1 4 6 8, tab 1 2 5 11),
   (tab 1 4 6 8, tab 1 6 2 8), (tab 1 4 6 8, tab 1 6 3 15), (tab 1 2 4 8, tab 1 6 2 8),
   (tab 1 2 4 8, tab 1 6 3 15)]

@[expose] def hasOrderFourProduct (M : List ℕ) : Bool :=
  pairs16.any fun bc =>
    let W := comp M (comp bc.1 (comp M bc.2))
    let W2 := comp W W
    W2 != idTab && comp W2 W2 == idTab

set_option maxRecDepth 100000 in
theorem hasOrderFourProduct_tab : ∀ a < 16, ∀ c < 16, ∀ d < 16,
    ((List.range 15).all fun k => vmul (k + 1) 2 a c d != 0) = true →
      hasOrderFourProduct (tab 2 a c d) = true := by
  decide +kernel

end CFSG.RankThree.GF2n.Parrott.FusionE16
