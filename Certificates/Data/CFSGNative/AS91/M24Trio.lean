module

public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def tTabs : List (Array Nat) :=
  [#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15, 21, 20, 23, 22, 17, 16, 19, 18],
    #[3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15, 19, 18, 17, 16, 23, 22, 21, 20],
    #[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 16, 17, 22, 23, 20, 21],
    #[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18],
    #[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19],
    #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21]]

@[expose] def sextU2 : List Nat := [85, 170, 21760, 43520, 5570560, 11141120]

@[expose] def sextU3 : List Nat := [51, 204, 13056, 52224, 3342336, 13369344]

@[expose] def sextsOfBase (_ : Unit := ()) : List Nat :=
  let S := sextList ()
  (List.range nSext).filter fun q => trioIn baseTrio S[q]!

@[expose] def genFixCheck (_ : Unit := ()) : Bool :=
  let S := sextList ()
  let thr := sextsOfBase ()
  thr.length == 7 &&
    tTabs.all fun t =>
      img t 255 == 255 && img t 65280 == 65280 && img t 16711680 == 16711680 &&
        thr.all fun q => imgSext t S[q]! == S[q]!

@[expose] def baseSextCheck (_ : Unit := ()) : Bool :=
  [baseSext, sextU2, sextU3].all fun U => trioIn baseTrio U && decide (sextIdx U < 1771)

@[expose] def orbitFive (steps : List (Nat → Nat)) (p : Nat) : List Nat :=
  ((bfs (fun i => i) steps p 1).1.toList).take 5

@[expose] def trioOrbitCheck (_ : Unit := ()) : Bool :=
  let T := trioList ()
  let steps := trioSteps tTabs
  (List.range nTrio).all fun p =>
    decide (1 < zc T[0]! T[p]!) ||
      (let c := orbitFive steps p
       c.length == 5 && decide c.Nodup && c.all (fun q => decide (q < 3795)) &&
         reachOK 3795 steps p c)

@[expose] def nTup : Nat := 759 * 759 * 1771 * 1771 * 1771

@[expose] def encTup (a b u v w : Nat) : Nat := a + 759 * (b + 759 * (u + 1771 * (v + 1771 * w)))

@[expose] def stepTup (O : Array Nat) (S : Array (List Nat)) (g : Array Nat) (c : Nat) : Nat :=
  let a := octIdx (img g O[c % 759]!)
  let b := octIdx (img g O[c / 759 % 759]!)
  let u := sextIdx (imgSext g S[c / 759 / 759 % 1771]!)
  let v := sextIdx (imgSext g S[c / 759 / 759 / 1771 % 1771]!)
  let w := sextIdx (imgSext g S[c / 759 / 759 / 1771 / 1771 % 1771]!)
  if a < 759 && b < 759 && u < 1771 && v < 1771 && w < 1771 then encTup a b u v w else nTup

@[expose] def tupSteps (gs : List (Array Nat)) : List (Nat → Nat) :=
  let O := octList ()
  let S := sextList ()
  gs.map fun g c => stepTup O S g c

@[expose] def x0Code (_ : Unit := ()) : Nat :=
  encTup (octIdx 255) (octIdx 65280) (sextIdx baseSext) (sextIdx sextU2) (sextIdx sextU3)

@[expose] def orbitTup (steps : List (Nat → Nat)) (x : Nat) : List Nat :=
  (bfs (fun i => i) steps x 5000).1.toList

@[expose] def tupOrbitCheck (_ : Unit := ()) : Bool :=
  let x0 := x0Code ()
  let steps := tupSteps lTabs
  let c := orbitTup steps x0
  decide (x0 < nTup) && decide (1008 ≤ c.length) && decide c.Nodup &&
    c.all (fun q => decide (q < nTup)) && reachOK nTup steps x0 c

@[expose] def trio12Check (_ : Unit := ()) : Bool :=
  genFixCheck () && baseSextCheck () && trioOrbitCheck () && tupOrbitCheck ()

end CFSG.Quasithin.H13.AS91.M24G.Native
