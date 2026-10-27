module

public import Certificates.Data.SolMaxSixGen

public section

namespace CFSG.ComponentClassification.SolMax.ThreeCent

open CFSG.PSL3Four.Native CFSG.ComponentClassification.SolMax.SixGen

@[expose] def threeCentCases : List (Swaps × List Swaps × Nat) := [
    ([(0, 1), (0, 2)],
      [[(0, 1), (0, 2)], [(3, 4)], [(3, 4), (3, 5), (3, 6), (3, 7), (3, 8)]], 2160),
    ([(0, 1), (0, 2), (3, 4), (3, 5)],
      [[(0, 1), (0, 2)], [(3, 4), (3, 5)], [(0, 3), (1, 4), (2, 5)], [(6, 7)], [(6, 7), (6, 8)]],
      108),
    ([(0, 1), (0, 2), (3, 4), (3, 5), (6, 7), (6, 8)],
      [[(0, 1), (0, 2)], [(3, 4), (3, 5)], [(6, 7), (6, 8)], [(0, 3), (1, 4), (2, 5)],
        [(3, 6), (4, 7), (5, 8)]], 162)]

@[expose] def threeCentSupp (t : Tab) : Nat := countBelow 9 fun i => t[i]! != i

@[expose] def threeCentCaseOK (c : Swaps × List Swaps × Nat) : Bool :=
  let u := tabOf (permOf c.1)
  let gs : Array Tab := (c.2.1.map fun l => tabOf (permOf l)).toArray
  let E := enumBFS 9 gs c.2.2
  let big := E.tabs.filter fun a =>
    comp 9 a a == idTab 9 && !(a == idTab 9) && 6 ≤ threeCentSupp a
  gs.all (fun g => commutes g u) && enumOK 9 gs E && E.tabs.size == c.2.2 &&
    E.tabs.all (fun y =>
      let y2 := comp 9 y y
      y2 == idTab 9 || !(comp 9 y2 y2 == idTab 9) || threeCentSupp y < 6 ||
        threeCentSupp y2 < 6) &&
    big.all (fun a => big.all fun b =>
      a == b || !commutes a b || threeCentSupp (comp 9 a b) < 6)

@[expose] def threeCentCheck : Bool := threeCentCases.all threeCentCaseOK

end CFSG.ComponentClassification.SolMax.ThreeCent
