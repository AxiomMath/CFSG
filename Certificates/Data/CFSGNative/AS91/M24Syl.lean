module

public import Certificates.Data.CFSGNative.AS91.M24Todd

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def treeValid {α : Type} [Inhabited α] [DecidableEq α] (valid : α → Bool)
    (steps : List (α → α)) (base : α) (r : Array α × Array Nat × Array Nat) : Bool :=
  decide (0 < r.1.size) && decide (r.1[0]! = base) && r.2.1.size == r.1.size &&
    r.2.2.size == r.1.size &&
    allLt r.1.size fun j => valid r.1[j]! && (j == 0 || (decide (r.2.1[j]! < j) &&
      decide (r.2.2[j]! < steps.length) &&
      decide ((steps.getD r.2.2[j]! id) r.1[r.2.1[j]!]! = r.1[j]!)))

@[expose] def s0Tabs : List (Array Nat) :=
  [#[0, 1, 2, 3, 7, 6, 5, 4, 14, 15, 12, 13, 9, 8, 11, 10, 23, 22, 21, 20, 16, 17, 18, 19],
    #[4, 5, 6, 7, 1, 0, 3, 2, 12, 13, 14, 15, 9, 8, 11, 10, 18, 19, 16, 17, 23, 22, 21, 20],
    #[4, 5, 7, 6, 1, 0, 2, 3, 12, 13, 15, 14, 9, 8, 10, 11, 23, 22, 20, 21, 18, 19, 17, 16],
    #[4, 5, 7, 6, 1, 0, 2, 3, 20, 21, 23, 22, 17, 16, 18, 19, 15, 14, 12, 13, 10, 11, 9, 8]]

@[expose] def pairPart : List Nat := [3, 12, 48, 192]

@[expose] def s0FixCheck (_ : Unit := ()) : Bool :=
  s0Tabs.all fun g => img g 255 == 255 && imgTrio g baseTrio == baseTrio &&
    imgSext g baseSext == baseSext && imgSext g pairPart == pairPart

@[expose] def imgTriple (g : Array Nat) (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (g[x.1]!, g[x.2.1]!, g[x.2.2]!)

@[expose] def keyTriple (x : Nat × Nat × Nat) : Nat := x.1 + 24 * (x.2.1 + 24 * x.2.2)

@[expose] def validTriple (x : Nat × Nat × Nat) : Bool :=
  decide (x.1 < 24) && decide (x.2.1 < 24) && decide (x.2.2 < 24)

@[expose] def tripleOrbitCheck (_ : Unit := ()) : Bool :=
  let steps := s0Tabs.map imgTriple
  let r := bfs keyTriple steps (0, 8, 16) 1100
  treeValid validTriple steps (0, 8, 16) r && decide (1024 ≤ r.1.size) &&
    decide (r.1.toList.map keyTriple).Nodup

abbrev OSP : Type := Nat × List Nat × List Nat

@[expose] def imgOSP (g : Array Nat) (x : OSP) : OSP :=
  (img g x.1, imgSext g x.2.1, imgSext g x.2.2)

@[expose] def keyOSP (x : OSP) : Nat := (x.1 <<< 240) ||| (keyL x.2.1 <<< 96) ||| keyL x.2.2

@[expose] def validOSP (x : OSP) : Bool :=
  decide (x.1 < 2 ^ 24) && x.2.1.all (fun m => decide (m < 2 ^ 24)) &&
    x.2.2.all (fun m => decide (m < 2 ^ 24)) && decide (x.2.1.Pairwise (· < ·)) &&
    decide (x.2.2.Pairwise (· < ·))

@[expose] def tup0 : OSP := (255, baseSext, pairPart)

@[expose] def tupleOrbitCheck (_ : Unit := ()) : Bool :=
  let steps := lTabs.map imgOSP
  let r := bfs keyOSP steps tup0 200
  treeValid validOSP steps tup0 r && decide (63 ≤ r.1.size) &&
    decide (r.1.toList.map keyOSP).Nodup

@[expose] def fixedCheck (_ : Unit := ()) : Bool :=
  (List.range 2048).all (fun m =>
    !(s0Tabs.all fun a => toddAct a m == m) || m == 0 || m == 31) &&
    s0Tabs.all fun a => toddAct a 31 == 31

@[expose] def clsOf (s : List Nat) : Nat := actM ccEColsN (s.headD 0)

@[expose] def clsTab (S : Array (List Nat)) : Array Nat := S.map clsOf

@[noinline, expose] def clsDistinctLoop (cl : Array Nat) : Bool :=
  allLt cl.size fun q => allLt q fun q' => cl[q]! != cl[q']!

@[expose] def clsDistinctCheck (_ : Unit := ()) : Bool :=
  let S := sextList ()
  let cl := clsTab S
  decide (cl.size = 1771) && clsDistinctLoop cl && clsOf baseSext == 31

@[expose] def sextsThrough (S : Array (List Nat)) (t : Nat × Nat × Nat) : List Nat :=
  (List.range nSext).filter fun q => trioIn t S[q]!

@[noinline, expose] def trioDetLoop (T : Array (Nat × Nat × Nat)) (S : Array (List Nat))
    (qs : List Nat) : Bool :=
  (List.range nTrio).all fun p => !(qs.all fun q => trioIn T[p]! S[q]!) || p == 0

@[expose] def trioDetCheck (_ : Unit := ()) : Bool :=
  let S := sextList ()
  let T := trioList ()
  let qs := sextsThrough S baseTrio
  trioDetLoop T S qs

@[expose] def v0List : List Nat := [0, 31, 160, 191, 320, 351, 480, 511]

@[expose] def vpList : List Nat := [0, 31, 224, 255, 320, 351, 416, 447]

@[expose] def closedXor (L : List Nat) : Bool := L.all fun a => L.all fun b => L.contains (a ^^^ b)

@[expose] def v0Check (_ : Unit := ()) : Bool :=
  let S := sextList ()
  let cl := clsTab S
  let qs := sextsThrough S baseTrio
  sortL (0 :: qs.map fun q => cl[q]!) == v0List && closedXor v0List && closedXor vpList

@[expose] def scTab (cl : Array Nat) : Array Bool :=
  (Array.range 2048).map fun m => cl.toList.contains m

@[expose] def sp8 (v w : Nat) : List Nat :=
  [0, 31, v, 31 ^^^ v, w, 31 ^^^ w, v ^^^ w, 31 ^^^ v ^^^ w]

@[expose] def spanCand (sc : Array Bool) (v w : Nat) : Bool :=
  sc[v]! && sc[31 ^^^ v]! && v != 0 && v != 31 && w != 0 && w != 31 && w != v && w != (31 ^^^ v) &&
    sc[w]! && sc[31 ^^^ w]! && sc[v ^^^ w]! && sc[31 ^^^ v ^^^ w]!

@[expose] def spanInv (tabs : List (Array Nat)) (v w : Nat) : Bool :=
  tabs.all fun T => (sp8 v w).contains T[v]! && (sp8 v w).contains T[w]!

@[noinline, expose] def spanRow (sc : Array Bool) (tabs : List (Array Nat)) (v w : Nat) : Bool :=
  !(spanCand sc v w) || (decide (sp8 v w).Nodup &&
    (!(spanInv tabs v w) || sortL (sp8 v w) == v0List || sortL (sp8 v w) == vpList))

@[noinline, expose] def spanLoop (sc : Array Bool) (tabs : List (Array Nat)) : Bool :=
  allLt 2048 fun v => allLt 2048 fun w => spanRow sc tabs v w

@[expose] def spanCheck (_ : Unit := ()) : Bool :=
  let S := sextList ()
  let sc := scTab (clsTab S)
  let tabs := s0Tabs.map fun a => (Array.range 2048).map (toddAct a)
  spanLoop sc tabs

@[expose] def stepSp (a : Array Nat) (L : List Nat) : List Nat := sortL (L.map (toddAct a))

@[expose] def keySp (L : List Nat) : Nat := L.foldl (fun acc m => (acc <<< 11) ||| m) 0

@[expose] def validSp (L : List Nat) : Bool :=
  L.all (fun m => decide (m < 2048)) && decide (L.Pairwise (· < ·)) && closedXor L &&
    L.contains 0

@[expose] def spaceOrbitCheck (_ : Unit := ()) : Bool :=
  let steps := genTabs.map stepSp
  let r := bfs keySp steps vpList 3000
  treeValid validSp steps vpList r && decide (3796 ≤ r.1.size) &&
    decide (r.1.toList.map keySp).Nodup

@[expose] def sylCheck (_ : Unit := ()) : Bool :=
  s0FixCheck () && tripleOrbitCheck () && tupleOrbitCheck () && fixedCheck () &&
    clsDistinctCheck () && trioDetCheck () && v0Check () && spanCheck () && spaceOrbitCheck ()

end CFSG.Quasithin.H13.AS91.M24G.Native
