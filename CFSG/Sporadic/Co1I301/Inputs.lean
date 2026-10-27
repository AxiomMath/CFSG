module

public import CFSG.Sporadic.Co1Patterson.GraphInputs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveFixRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public import Certificates.Data.U42Presentation

public section

namespace CFSG.Sporadic.Co1I301.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Patterson.Native

@[expose] def cWordsN : List (List Nat) :=
  [
    [
      38, 31, 35, 32, 27, 28, 24, 33],
    [
      40, 40, 40, 40, 40, 40, 40, 40],
    [
      32, 30, 28, 26, 36, 26, 24, 24, 24, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 24, 26,
      32, 32, 32, 28, 38, 36, 24, 30, 32, 26, 34, 30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28,
      38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 28, 36, 24, 26, 32, 38, 32, 38, 26, 24,
      24, 24, 24, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 32, 26, 34, 30, 28, 28, 24, 32,
      24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 32, 26, 34,
      30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36,
      24, 30, 28, 36, 24, 26, 32, 38, 32, 38, 26, 24, 24, 24, 24, 24, 24, 24, 26, 32, 32, 32, 28,
      38, 36, 24, 30, 32, 26, 34, 30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30,
      26, 32, 32, 32, 28, 38, 36, 24, 30],
    [
      24, 30, 38, 28, 26, 26, 26, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36,
      24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32,
      32, 32, 28, 38, 36, 24, 30, 32, 26, 34, 30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28, 38,
      36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 32, 26, 34, 30, 28, 28, 24, 32, 24, 24, 26,
      32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 30, 34, 38, 24, 26, 36,
      28, 24, 26, 26, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26,
      32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 24, 24, 24, 26, 32, 32,
      32, 28, 38, 36, 24, 30, 28, 36, 24, 26, 32, 38, 32, 38, 26, 24, 24, 24, 24, 24, 24, 24, 26,
      32, 32, 32, 28, 38, 36, 24, 30, 28, 36, 24, 26, 32, 38, 32, 38, 26, 24, 24, 24, 24, 24, 24,
      24, 26, 32, 32, 32, 28, 38, 36, 24, 30],
    [
      31, 25, 37, 39, 29, 33, 33, 33, 27, 31, 25, 37, 39, 29, 33, 33, 33, 27, 25, 25, 33, 25, 29,
      29, 31, 35, 27, 33, 31, 25, 37, 39, 29, 33, 33, 33, 27, 25, 25, 25, 25, 25, 25, 25, 27, 39,
      33, 39, 33, 27, 25, 37, 29, 31, 25, 37, 39, 29, 33, 33, 33, 27, 31, 25, 37, 39, 29, 33, 33,
      33, 27, 25, 25, 33, 25, 29, 29, 31, 35, 27, 33, 31, 25, 37, 39, 29, 33, 33, 33, 27, 25, 25,
      25, 25, 25, 25, 25, 27, 39, 33, 39, 33, 27, 25, 37, 29, 31, 25, 37, 39, 29, 33, 33, 33, 27,
      25, 25, 25, 31, 25, 37, 39, 29, 33, 33, 33, 27, 31, 25, 37, 39, 29, 33, 33, 33, 27, 31, 25,
      37, 39, 29, 33, 33, 33, 27, 31, 25, 37, 39, 29, 33, 33, 33, 27, 27, 27, 25, 29, 37, 27, 25,
      39, 35, 31, 31, 25, 37, 39, 29, 33, 33, 33, 27, 25, 25, 25, 31, 25, 37, 39, 29, 33, 33, 33,
      27, 31, 25, 37, 39, 29, 33, 33, 33, 27, 31, 25, 37, 39, 29, 33, 33, 33, 27, 31, 25, 37, 39,
      29, 33, 33, 33, 27, 27, 27, 25, 29, 37, 27, 25, 39, 35, 31, 31, 25, 37, 39, 29, 33, 33, 33,
      27, 31, 25, 37, 39, 29, 33, 33, 33, 27, 25, 31, 25, 37, 39, 29, 33, 33, 33, 27, 25, 31, 25,
      37, 39, 29, 33, 33, 33, 27, 31, 25, 37, 39, 29, 33, 33, 33, 27, 29, 29, 25, 27, 25],
    [
      32, 32, 36, 26, 32, 32, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24,
      30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 24, 24, 24, 24,
      26, 32, 32, 32, 28, 38, 36, 24, 30, 24, 32, 26, 34, 30, 28, 28, 24, 32, 24, 24, 26, 32, 32,
      32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 32, 26, 34, 30, 28, 28, 24, 32,
      24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 32, 26, 34,
      30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36,
      24, 30, 32, 26, 34, 30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32,
      32, 32, 28, 38, 36, 24, 30, 32, 26, 34, 30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28, 38,
      36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 28, 36, 24, 26, 32, 38, 32, 38, 26, 24, 24,
      24, 24, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 30, 34, 38, 24, 26, 36, 28, 24, 26,
      26, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32,
      28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 24, 24, 24, 26, 32, 32, 32, 28, 38,
      36, 24, 30],
    [
      30, 26, 36, 36, 24, 30, 24, 24, 24, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32,
      32, 32, 28, 38, 36, 24, 30, 25, 30, 34, 38, 24, 26, 36, 28, 24, 26, 26, 26, 32, 32, 32, 28,
      38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26,
      32, 32, 32, 28, 38, 36, 24, 30, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 32, 26, 34,
      30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36,
      24, 30, 30, 34, 38, 24, 26, 36, 28, 24, 26, 26, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32,
      32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36,
      24, 30, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 32, 26, 34, 30, 28, 28, 24, 32, 24,
      24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 28, 36, 24, 26,
      32, 38, 32, 38, 26, 24, 24, 24, 24, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 32, 26,
      34, 30, 28, 28, 24, 32, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38,
      36, 24, 30, 30, 34, 38, 24, 26, 36, 28, 24, 26, 26, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26,
      32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38, 36, 24, 30, 26, 32, 32, 32, 28, 38,
      36, 24, 30, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 28, 36, 24, 26, 32, 38, 32, 38,
      26, 24, 24, 24, 24, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30, 28, 36, 24, 26, 32, 38,
      32, 38, 26, 24, 24, 24, 24, 24, 24, 24, 26, 32, 32, 32, 28, 38, 36, 24, 30],
    [
      20, 14, 8],
    [
      22, 20, 16, 12],
    [
      21, 22, 18, 16, 12, 8],
    [
      22, 16, 14, 8],
    [
      21, 18, 12, 8],
    [
      20, 16, 12, 8]]

@[expose] def cDag (_ : Unit := ()) : List Rows × List Rows × Bool :=
  dag gBase (cWordsN.map decWord)

@[expose] def cEl (D : List Rows × List Rows × Bool) (j : Nat) : Rows := D.1.getD (j - 1) one

@[expose] def cR : Fin 6 → Fin 6 → ZMod 2 :=
  ![![0, 0, 1, 0, 1, 0], ![0, 0, 1, 1, 1, 1], ![1, 1, 0, 1, 1, 0], ![0, 1, 1, 0, 1, 1],
    ![1, 1, 1, 1, 0, 1], ![0, 1, 0, 1, 1, 0]]

@[expose] def rootFix : List (Nat × Nat) := [(0, 25668), (1, 452), (2, 17819)]

@[expose] def conjTree (G Gi : Array Rows) (root : Rows) (cap : Nat) : Array Nat × Array Nat :=
  Id.run do
    let mut pts : Array Rows := #[root]
    let mut seen : Std.HashSet (Array Nat) := ({} : Std.HashSet (Array Nat)).insert root
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    for i in [0:cap] do
      if h : i < pts.size then
        let x := pts[i]
        for l in [0:G.size] do
          let y := mul (mul G[l]! x) Gi[l]!
          if !seen.contains y then
            seen := seen.insert y
            pts := pts.push y
            par := par.push i
            lab := lab.push l
    return (par, lab)

@[expose] def relRows (x y xi yi : Rows) (w : List (Fin 2 × Bool)) : Rows :=
  w.foldl (fun acc l => mul acc (if l.1 = 0 then (if l.2 then x else xi) else
    (if l.2 then y else yi))) one

@[expose] def aRw : Rows := iotaARows

@[expose] def dRw (_ : Unit := ()) : Rows := cEl (cDag ()) 21

@[expose] def k1Rw (_ : Unit := ()) : Rows := cEl (cDag ()) 22

@[expose] def k2Rw (_ : Unit := ()) : Rows := cEl (cDag ()) 23

@[expose] def eRw (i : Nat) : Rows := cEl (cDag ()) (24 + i)

@[expose] def rRw (i : Nat) : Rows := cEl (cDag ()) (27 + i)

@[expose] def r0Gens (_ : Unit := ()) : Array Rows := (aRw :: (List.range 6).map rRw).toArray

@[expose] def r0Tree (_ : Unit := ()) : GTree := gtBFS (r0Gens ()) 128

@[expose] def r0Set (_ : Unit := ()) : Std.HashSet (Array Nat) :=
  Std.HashSet.ofList (r0Tree ()).pts.toList

@[expose] def dOrb (_ : Unit := ()) : Orb :=
  mkOrbT brayArr brayInvArr (dRw ()) (conjTree brayArr brayInvArr (dRw ()) 8960)

@[expose] def commR (x y : Rows) : Bool := mul x y == mul y x

@[expose] def chkDag (_ : Unit := ()) : Bool :=
  (cDag ()).2.2 && (cDag ()).1.length == 32 &&
    (List.range 32).all (fun j => validRows (cEl (cDag ()) (j + 1)))

@[expose] def chkD (_ : Unit := ()) : Bool :=
  pow (dRw ()) 3 == one && dRw () != one && commR (dRw ()) aRw &&
    CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCheck (dRw ()) one
      (inv (CFSG.HardMathSupport.Dickson.I271.TabMFive.subOneRows (dRw ()))) 24

@[expose] def chkRoots (_ : Unit := ()) : Bool :=
  rootFix.all fun p => p.2 != 0 &&
    act (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows p.1) p.2 == p.2

@[expose] def chkOrbit (_ : Unit := ()) : Bool :=
  orbOK brayArr brayInvArr (dRw ()) (dOrb ()) && (dOrb ()).c.pts.size == 8960

@[expose] def chkR0 (_ : Unit := ()) : Bool :=
  gtOK (r0Gens ()) (r0Tree ()) && (r0Tree ()).pts.size == 128 &&
    (List.range 6).all (fun i => commR (rRw i) (dRw ()) && qPts.contains (rRw i) &&
      mul (rRw i) (rRw i) == one) &&
    twoAQTree.pts.all (fun x => !commR x (dRw ()) || (r0Set ()).contains x) &&
    (List.finRange 6).all (fun i => (List.finRange 6).all fun j =>
      mul (rRw i) (rRw j) == mul (mul (rRw j) (rRw i)) (if cR i j = 1 then aRw else one))

@[expose] def chkK (_ : Unit := ()) : Bool :=
  commR (k1Rw ()) (dRw ()) && commR (k1Rw ()) aRw && commR (k2Rw ()) (dRw ()) &&
    commR (k2Rw ()) aRw &&
    CFSG.HardMathSupport.Dickson.I271.U42Presentation.u42Words.all
      (fun w => validRows (relRows (k1Rw ()) (k2Rw ()) (inv (k1Rw ())) (inv (k2Rw ())) w) &&
        (r0Set ()).contains (relRows (k1Rw ()) (k2Rw ()) (inv (k1Rw ())) (inv (k2Rw ())) w)) &&
    !(r0Set ()).contains (k1Rw ()) && mul (k1Rw ()) (inv (k1Rw ())) == one &&
    mul (k2Rw ()) (inv (k2Rw ())) == one

@[expose] def chkE (_ : Unit := ()) : Bool :=
  (List.range 3).all (fun i => pow (eRw i) 3 == one && commR (eRw i) (dRw ()) &&
      commR (eRw i) aRw) &&
    (List.range 3).all (fun i => (List.range 3).all fun j => commR (eRw i) (eRw j)) &&
    (List.range 81).all (fun n => n == 0 ||
      mul (mul (mul (pow (dRw ()) (n % 3)) (pow (eRw 0) (n / 3 % 3)))
        (pow (eRw 1) (n / 9 % 3))) (pow (eRw 2) (n / 27 % 3)) != one)

@[expose] def co1RowCheck (_ : Unit := ()) : Bool :=
  chkDag () && chkD () && chkRoots () && chkOrbit () && chkR0 () && chkK () && chkE ()

end CFSG.Sporadic.Co1I301.Native
