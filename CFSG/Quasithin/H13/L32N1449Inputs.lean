module

public import CFSG.Quasithin.H13.L32NO3Inputs

public section

namespace CFSG.Quasithin.H13.Q1449Cert

open Mat8Cert S7Cert S8Cert G5Cert O3Cert

@[expose] def xsB : Bool :=
  [0, 1].all fun c => (wE c).contains (xsS c) && !(om3FE.contains (xsS c)) &&
    mul8 (xsS c) (xsS c) == one8

@[expose] def cPWB : Bool :=
  [0, 1].all fun c =>
    let hW : Std.HashSet (List ℕ) := Std.HashSet.ofList (wE c)
    (pE c).all fun p => hW.contains p ||
      !((cxs c (xsS c) ++ [xsS c]).all fun w => mul8 p w == mul8 w p)

@[expose] def alt0B : Bool :=
  [0, 1].all fun c => (List.range 256).all fun n => !(b5N (mv8 (xsS c) n) n)

@[expose] def expB : Bool :=
  [0, 1].all fun c =>
    ((gamE c).filter fun x => mul8 x (xsS c) == mul8 (xsS c) x).all fun x => pow8 x 240 == one8

@[expose] def cjL (c : ℕ) : List (List ℕ × List ℕ × List ℕ) :=
  if c = 0 then
    [([2, 1, 19, 50, 7, 14, 233, 151], [1, 2, 4, 8, 16, 32, 64, 128],
        [1, 2, 4, 8, 16, 32, 64, 128]),
      ([76, 200, 4, 12, 151, 126, 9, 7], [4, 8, 3, 1, 136, 204, 17, 34],
        [8, 12, 1, 2, 72, 140, 49, 18]),
      ([85, 255, 90, 245, 119, 238, 121, 231], [4, 8, 6, 11, 204, 68, 221, 102],
        [15, 5, 1, 2, 95, 165, 33, 50]),
      ([107, 214, 221, 187, 231, 158, 153, 119], [4, 8, 9, 14, 68, 136, 153, 238],
        [6, 11, 1, 2, 102, 187, 17, 34])]
  else
    [([3, 2, 17, 51, 7, 14, 153, 119], [1, 2, 4, 8, 16, 32, 64, 128],
        [1, 2, 4, 8, 16, 32, 64, 128]),
      ([90, 245, 85, 255, 214, 189, 221, 187], [4, 8, 5, 10, 76, 132, 95, 165],
        [5, 10, 1, 2, 95, 165, 19, 33]),
      ([109, 219, 221, 187, 165, 95, 85, 255], [4, 8, 10, 15, 192, 64, 80, 160],
        [13, 6, 1, 2, 96, 176, 32, 48]),
      ([112, 224, 153, 119, 48, 32, 17, 51], [4, 8, 15, 5, 136, 204, 85, 170],
        [9, 14, 1, 2, 121, 158, 49, 18])]

@[expose] def cjB : Bool :=
  [0, 1].all fun c =>
    let hG : Std.HashSet (List ℕ) := Std.HashSet.ofList (gamE c)
    let h3 : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
    (wE c).all fun w => h3.contains w || (cjL c).any fun t =>
      t.1 == w && hG.contains t.2.1 && mul8 t.2.1 t.2.2 == one8 &&
        mul8 (mul8 t.2.1 w) t.2.2 == xsS c

@[expose] def aL (c : ℕ) : List (List ℕ) :=
  ((gamE c).filter fun x => mul8 x (xsS c) == mul8 (xsS c) x).filter fun x => pow8 x 15 == one8

@[expose] def x0AB : Bool := [0, 1].all fun c => !((elemsOf (aL c)).contains (xsS c))

@[expose] def betaC (c : ℕ) : List ℕ :=
  if c = 0 then [30, 30, 6, 10, 6, 18, 3, 6] else [30, 0, 24, 10, 6, 18, 3, 17]

@[expose] def fiveS (c : ℕ) : List ℕ := if c = 0 then [1, 65, 69, 73, 76] else [1, 65, 68, 73, 77]

@[expose] def fL : List ℕ := [30, 29, 27, 23, 15]

@[expose] def evenB (v : ℕ) : Bool :=
  (v.testBit 0 ^^ v.testBit 1 ^^ v.testBit 2 ^^ v.testBit 3 ^^ v.testBit 4) == false && v < 32

@[expose] def betaB : Bool :=
  [0, 1].all fun c =>
    let S := spanN (imgBasis (xsS c))
    ((List.range 256).all fun v => (mv8 (betaC c) v == 0) == S.contains v) &&
      ((List.range 256).all fun v => evenB (mv8 (betaC c) v)) &&
      (List.range 5).all fun j => mv8 (betaC c) ((fiveS c).getD j 0) == fL.getD j 0

@[expose] def sigOf (c : ℕ) (a : List ℕ) : List ℕ :=
  (List.range 5).map fun j => fL.idxOf (mv8 (betaC c) (mv8 a ((fiveS c).getD j 0)))

@[expose] def sigB : Bool :=
  [0, 1].all fun c => (elemsOf (aL c)).all fun a =>
    ((List.range 5).all fun j => fL.contains (mv8 (betaC c) (mv8 a ((fiveS c).getD j 0)))) &&
      (!(sigOf c a == [0, 1, 2, 3, 4]) || a == one8)

@[expose] def irrB : Bool :=
  [0, 1].all fun c =>
    let S := spanN (imgBasis (xsS c))
    let E := elemsOf (aL c)
    (List.range 256).all fun v =>
      S.contains v ||
        (let h : Std.HashSet ℕ := Std.HashSet.ofList
            (spanN (E.map (fun a => mv8 a v) ++ imgBasis (xsS c)))
         (List.range 256).all h.contains)

@[expose] def o5L (c : ℕ) : List (List ℕ) := (gamE c).filter fun a => pow8 a 5 == one8 && a != one8

@[expose] def small64B (x : List ℕ) : Bool :=
  smallImgB x && decide (64 ≤ ((List.range 256).filter fun u => mv8 x u == u).length)

@[expose] def fullAltB (x : List ℕ) : Bool :=
  fullImgB x && (List.range 256).all fun n => !(b5N (mv8 x n) n)

@[expose] def invRkB : Bool :=
  [0, 1].all fun c =>
    let O := o5L c
    (gamE c).all fun x =>
      x == one8 || !(mul8 x x == one8) || small64B x || fullAltB x ||
        O.all fun a => !(mul8 a x == mul8 x a)

@[expose] def q1449Check : Bool :=
  xsB && cPWB && alt0B && expB && cjB && x0AB && betaB && sigB && irrB && invRkB

end CFSG.Quasithin.H13.Q1449Cert
