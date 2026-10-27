module

public import CFSG.Quasithin.H13.L32NG5Inputs

public section

namespace CFSG.Quasithin.H13.G5ACert

open Mat8Cert S7Cert S8Cert G5Cert

@[expose] def q5ac : List ℕ := [0, 0, 0, 0, 14, 13, 11, 7]

@[expose] def quadA (v : ℕ) : Bool := dotN v (mv8 q5ac v)

@[expose] def b5A (v w : ℕ) : Bool := quadA (v ^^^ w) ^^ quadA v ^^ quadA w

@[expose] def gSAG : List (List ℕ) :=
  [[1, 2, 4, 8, 17, 34, 68, 136], [16, 32, 64, 128, 1, 2, 4, 8], [2, 1, 4, 8, 32, 16, 64, 128],
    [3, 5, 9, 1, 48, 80, 144, 16]]

@[expose] def gAAG : List (List ℕ) :=
  [[1, 2, 4, 8, 17, 34, 68, 136], [16, 32, 64, 128, 1, 2, 4, 8], [2, 4, 1, 8, 32, 64, 16, 128],
    [3, 5, 9, 1, 48, 80, 144, 16]]

@[expose] def gSAE : List (List ℕ) := elemsOf gSAG

@[expose] def gAAE : List (List ℕ) := elemsOf gAAG

@[expose] def gGA (b : Bool) : List (List ℕ) := if b then gSAG else gAAG

@[expose] def gEA (b : Bool) : List (List ℕ) := if b then gSAE else gAAE

@[expose] def nGA (b : Bool) : ℕ := if b then 720 else 360

@[expose] def basicAB : Bool :=
  [true, false].all fun b => subB (gGA b) (gEA b) && (gEA b).length == nGA b

@[expose] def pSAG : List (List ℕ) :=
  [[1, 2, 4, 8, 17, 34, 68, 136], [9, 3, 1, 5, 144, 48, 16, 80],
    [9, 10, 12, 8, 144, 160, 192, 128]]

@[expose] def pAAG : List (List ℕ) :=
  [[1, 2, 4, 8, 17, 34, 68, 136], [1, 3, 9, 5, 16, 48, 144, 80],
    [12, 6, 4, 5, 192, 96, 64, 80]]

@[expose] def pGA (b : Bool) : List (List ℕ) := if b then pSAG else pAAG

@[expose] def pEA (b : Bool) : List (List ℕ) := elemsOf (pGA b)

@[expose] def nPA (b : Bool) : ℕ := if b then 16 else 8

@[expose] def vA : ℕ := 13

@[expose] def pAB : Bool :=
  [true, false].all fun b =>
    let hG : Std.HashSet (List ℕ) := Std.HashSet.ofList (gEA b)
    subB (pGA b) (pEA b) && (pEA b).length == nPA b && (pGA b).all hG.contains &&
      (List.range 256).all fun v => !((pGA b).all fun p => mv8 p v == v) || v == 0 || v == vA

@[expose] def mRepsSA : List (List ℕ) :=
  [[16, 32, 64, 128, 1, 2, 4, 8], [1, 2, 8, 4, 16, 32, 128, 64]]

@[expose] def mRepsAA : List (List ℕ) :=
  [[16, 32, 64, 128, 1, 2, 4, 8], [4, 2, 8, 1, 64, 32, 128, 16]]

@[expose] def mRA (b : Bool) : List (List ℕ) := if b then mRepsSA else mRepsAA

@[expose] def mEA (b : Bool) (i : ℕ) : List (List ℕ) := elemsOf (pGA b ++ [(mRA b).getD i one8])

@[expose] def ovAB : Bool :=
  [true, false].all fun b =>
    let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList (pEA b)
    let hM : List (Std.HashSet (List ℕ)) := [0, 1].map fun i => Std.HashSet.ofList (mEA b i)
    let hG : Std.HashSet (List ℕ) := Std.HashSet.ofList (gEA b)
    (mRA b).length == 2 && (mRA b).all hG.contains &&
    ([0, 1].all fun i => (mEA b i).length == 3 * nPA b &&
      subB (pGA b ++ [(mRA b).getD i one8]) (mEA b i)) &&
    (gEA b).all fun y => hP.contains y ||
      (let B := elemsOf (pGA b ++ [y]) (3 * nPA b + 1)
       (3 * nPA b + 1 ≤ B.length && nodupB B) ||
         (B.length == 3 * nPA b && nodupB B && hM.any fun h => B.all h.contains))

@[expose] def oEA (b : Bool) (i : ℕ) : List (List ℕ) := elemsOf (oddOf (mEA b i))

@[expose] def wA : ℕ × ℕ := (208, 221)

@[expose] def oAB : Bool :=
  [true, false].all fun b =>
    let O0 := oEA b 0
    let O1 := oEA b 1
    subB (oddOf (mEA b 0)) O0 && subB (oddOf (mEA b 1)) O1 && O0.length == 3 &&
      O1.length == 12 &&
      O0.all (fun y => [vA, wA.1, wA.2].contains (mv8 y vA)) &&
      O0.any (fun y => mv8 y vA == wA.1) && O0.any (fun y => mv8 y vA == wA.2) &&
      O1.all (fun y => [vA, wA.1, wA.2].all fun v => mv8 y v == v) &&
      O0.all fun x => O1.all fun y => mul8 x y == mul8 y x

@[expose] def kAG : List (List ℕ) :=
  [[2, 4, 1, 8, 32, 64, 16, 128], [3, 5, 9, 1, 48, 80, 144, 16]]

@[expose] def kAE : List (List ℕ) := elemsOf kAG

@[expose] def kAP : List (List ℕ × List ℕ) :=
  kAE.map fun k => (k, (kAE.find? fun y => mul8 k y == one8).getD one8)

@[expose] def conjA (x : List ℕ) : List (List ℕ) :=
  kAP.map fun p => mul8 (mul8 p.1 x) p.2

@[expose] def kAB : Bool :=
  subB kAG kAE && kAE.length == 60 &&
    kAP.all (fun p => mul8 p.1 p.2 == one8 && validB p.2) &&
    ([true, false].all fun b =>
      let hG : Std.HashSet (List ℕ) := Std.HashSet.ofList (gEA b)
      kAG.all hG.contains &&
      (gGA b).all fun g =>
        let hKg : Std.HashSet (List ℕ) := Std.HashSet.ofList (kAE.map fun k => mul8 k g)
        kAE.all fun k => hKg.contains (mul8 g k)) &&
    (kAE.all fun x => x == one8 ||
      (subB (conjA x) (elemsOf (conjA x)) && (elemsOf (conjA x)).length == 60)) &&
    kAE.any (fun k => mv8 k vA != vA) &&
    [true, false].all fun b =>
      kAP.all fun p => (mEA b 1).contains p.1 ||
        kAE.any fun q => (pEA b).contains q &&
          !(kAE.contains (mul8 (mul8 p.1 q) p.2) && (pEA b).contains (mul8 (mul8 p.1 q) p.2))

@[expose] def g5aCheck : Bool := basicAB && pAB && ovAB && oAB && kAB

end CFSG.Quasithin.H13.G5ACert
