module

public import Certificates.Data.SolMaxThreeCent

public section

namespace CFSG.ComponentClassification.SolMax.EightPerm

open CFSG.PSL3Four.Native CFSG.ComponentClassification.SolMax.SixGen
  CFSG.ComponentClassification.SolMax.ThreeCent

@[expose] def eightPermCases : List (Swaps × List Swaps × Nat) := [
    ([(0, 1), (2, 3), (4, 5)], centGens, 288),
    ([(0, 1), (2, 3), (4, 5), (6, 7)],
      [[(0, 1)], [(0, 2), (1, 3)], [(2, 4), (3, 5)], [(4, 6), (5, 7)]], 384)]

@[expose] def eightAdmissible (u w : Tab) : Bool :=
  comp 9 w w == u ||
    (comp 9 w w == idTab 9 && 5 ≤ threeCentSupp w && 5 ≤ threeCentSupp (comp 9 w u))

@[expose] def eightLinked (u a b : Tab) : Bool :=
  commutes a b && !(comp 9 a b == idTab 9) && !(comp 9 a b == u)

@[expose] def eightPermCaseOK (c : Swaps × List Swaps × Nat) : Bool :=
  let u := tabOf (permOf c.1)
  let gs : Array Tab := (c.2.1.map fun l => tabOf (permOf l)).toArray
  let E := enumBFS 9 gs c.2.2
  let A := E.tabs.filter (eightAdmissible u)
  gs.all (fun g => commutes g u) && enumOK 9 gs E && E.tabs.size == c.2.2 &&
    A.all (fun a => A.all fun b => !eightLinked u a b || A.all fun c =>
      !(eightLinked u a c && eightLinked u b c) || A.all fun d =>
        !(eightLinked u a d && eightLinked u b d && eightLinked u c d))

@[expose] def eightPermCheck (_ : Unit := ()) : Bool := eightPermCases.all eightPermCaseOK

end CFSG.ComponentClassification.SolMax.EightPerm
