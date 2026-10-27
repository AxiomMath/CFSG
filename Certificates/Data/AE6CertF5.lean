module

public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import Mathlib.Data.List.Defs
public import Mathlib.Data.List.Permutation

public section

namespace Certificates.AE6Model

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def fLetterHat : List (List ℕ) :=
  [[3, 4, 5, 0, 1, 2, 9, 11, 10, 6, 8, 7], [4, 5, 3, 2, 0, 1, 11, 10, 9, 8, 7, 6],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [6, 7, 8, 9, 11, 10, 0, 1, 2, 3, 5, 4],
    [8, 6, 7, 10, 9, 11, 1, 2, 0, 4, 3, 5], [9, 10, 11, 6, 8, 7, 3, 5, 4, 0, 1, 2],
    [11, 9, 10, 7, 6, 8, 4, 3, 5, 1, 2, 0]]

@[expose] def fGammaHat : List (List ℕ) :=
  [[9, 11, 10, 3, 4, 5, 6, 7, 8, 0, 2, 1], [6, 8, 7, 3, 4, 5, 0, 2, 1, 9, 10, 11]]

@[expose] def listTable (l : List ℕ) : Table := (l.map UInt32.ofNat).toArray

@[expose] def lhTabs : List Table := fLetterHat.map listTable

@[expose] def ghTabs : List Table := fGammaHat.map listTable

@[expose] def fC (_ : Unit := ()) : Array Table × Array ℕ × Array ℕ :=
  mulClosureH 12 lhTabs.toArray 1000

@[expose] def fH0 (_ : Unit := ()) : Array Table × Array ℕ × Array ℕ :=
  mulClosureH 12 (lhTabs ++ ghTabs).toArray 3000

@[expose] def fCs : List (List ℕ) :=
  [[3, 4, 5, 1, 2, 0, 9, 11, 10, 7, 6, 8], [3, 4, 5, 0, 1, 2, 10, 9, 11, 8, 7, 6],
    [6, 7, 8, 10, 9, 11, 0, 1, 2, 5, 4, 3], [9, 10, 11, 7, 6, 8, 4, 3, 5, 2, 0, 1],
    [4, 5, 3, 2, 0, 1, 9, 11, 10, 7, 6, 8], [7, 8, 6, 9, 11, 10, 2, 0, 1, 4, 3, 5],
    [9, 10, 11, 8, 7, 6, 5, 4, 3, 1, 2, 0], [5, 3, 4, 1, 2, 0, 9, 11, 10, 8, 7, 6],
    [8, 6, 7, 9, 11, 10, 1, 2, 0, 5, 4, 3], [10, 11, 9, 6, 8, 7, 3, 5, 4, 1, 2, 0]]

@[expose] def csTabs : List Table := fCs.map listTable

@[expose] def perms4 : List (List ℕ) := List.permutations (List.range 4)

@[expose] def perms3 : List (List ℕ) := List.permutations (List.range 3)

@[expose] def wTable (πl : List ℕ) (ρs : List (List ℕ)) : Table :=
  Array.ofFn (n := 12) fun i =>
    UInt32.ofNat (3 * πl.getD (i.val / 3) 0 + (ρs.getD (i.val / 3) []).getD (i.val % 3) 0)

@[expose] def wEnum (_ : Unit := ()) : List Table :=
  let R := List.sections (List.replicate 4 perms3)
  perms4.flatMap fun πl => R.map (wTable πl)

@[expose] def weight1T (T : Table) : Bool :=
  (List.range 12).all (fun i => ap T i / 3 == i / 3) &&
    ((List.range 4).any fun b => (List.range 12).all fun i => i / 3 == b || ap T i == i) &&
    !tblEq 12 T (idT 12) && tblEq 12 (compT 12 T (compT 12 T T)) (idT 12)

@[expose] def pw1Go (U : Table) : ℕ → Table → Bool
  | 0, t => weight1T t
  | k + 1, t => weight1T t || pw1Go U k (compT 12 t U)

@[expose] def pw1 (U : Table) : Bool := pw1Go U 11 U

@[expose] def fF5 (_ : Unit := ()) : Bool :=
  let C := fC ()
  let H := fH0 ()
  mulTreeOK 12 lhTabs.toArray C.1 C.2.1 C.2.2 &&
    mulTreeOK 12 (lhTabs ++ ghTabs).toArray H.1 H.2.1 H.2.2 &&
    csTabs.all (fun c => C.1.any (tblEq 12 c)) &&
    (wEnum ()).all fun S =>
      let Si := invT 12 S
      invOK 12 S Si && (H.1.any (tblEq 12 S) || lhTabs.any fun X =>
        let Y := compT 12 (compT 12 S X) Si
        csTabs.any fun c => pw1 (compT 12 Y c))

end Certificates.AE6Model
