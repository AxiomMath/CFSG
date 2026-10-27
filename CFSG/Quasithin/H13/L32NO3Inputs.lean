module

public import CFSG.Quasithin.H13.L32NG5Inputs

public section

namespace CFSG.Quasithin.H13.O3Cert

open Mat8Cert S7Cert S8Cert G5Cert

@[expose] def o3G : List (List ℕ) :=
  [[1, 2, 4, 8, 17, 34, 68, 136],
    [16, 32, 64, 128, 1, 2, 4, 8],
    [2, 3, 8, 12, 48, 16, 192, 64],
    [1, 2, 5, 10, 16, 32, 80, 160],
    [4, 8, 1, 2, 64, 128, 16, 32],
    [2, 3, 12, 4, 32, 48, 192, 64]]

@[expose] def fG : List ℕ := [1, 3, 4, 12, 16, 48, 64, 192]

@[expose] def sG : List ℕ := [1, 2, 16, 32, 4, 8, 64, 128]

@[expose] def sfG : List ℕ := mul8 sG fG

@[expose] def om3E : List (List ℕ) := elemsOf o3G

@[expose] def om3FE : List (List ℕ) := elemsOf (o3G ++ [fG])

@[expose] def omNE : List (List ℕ) := elemsOf (o3G ++ [fG, sG])

@[expose] def h1E : List (List ℕ) := elemsOf (o3G ++ [sG])

@[expose] def h2E : List (List ℕ) := elemsOf (o3G ++ [sfG])

@[expose] def pow8 (x : List ℕ) : ℕ → List ℕ
  | 0 => one8
  | k + 1 => mul8 x (pow8 x k)

@[expose] def imgBasis (x : List ℕ) : List ℕ := (List.range 8).map fun j => mv8 x (2 ^ j) ^^^ 2 ^ j

@[expose] def smallImgB (x : List ℕ) : Bool :=
  let S := spanN (imgBasis x)
  decide (S.length ≤ 4) && (List.range 256).all fun n => S.contains (mv8 x n ^^^ n)

@[expose] def basicB : Bool :=
  let h : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
  subB o3G om3E && om3E.length == 3600 &&
    subB (o3G ++ [fG]) om3FE && om3FE.length == 7200 &&
    subB (o3G ++ [fG, sG]) omNE && omNE.length == 14400 &&
    subB (o3G ++ [sG]) h1E && h1E.length == 7200 &&
    subB (o3G ++ [sfG]) h2E && h2E.length == 7200 &&
    mul8 sG sG == one8 && mul8 fG fG == one8 && mul8 sG fG == mul8 fG sG &&
    omNE.all fun x => h.contains x || h.contains (mul8 sG x) || h.contains (mul8 fG x) ||
      h.contains (mul8 sfG x)

@[expose] def h1B : Bool :=
  let hF : Std.HashSet (List ℕ) := Std.HashSet.ofList om3FE
  h1E.all fun x => hF.contains x || !(mul8 x x == one8) || smallImgB x

@[expose] def gamE (c : ℕ) : List (List ℕ) := if c = 0 then h2E else omNE

@[expose] def pG (c : ℕ) : List (List ℕ) :=
  if c = 0 then
    [[2, 1, 19, 50, 7, 14, 233, 151],
      [5, 15, 250, 165, 7, 14, 233, 151],
      [6, 11, 10, 15, 96, 176, 160, 240]]
  else
    [[1, 2, 34, 51, 13, 6, 102, 187],
      [3, 2, 12, 8, 33, 19, 132, 76],
      [5, 10, 4, 8, 80, 160, 64, 128],
      [7, 14, 12, 8, 233, 151, 132, 76]]

@[expose] def pE (c : ℕ) : List (List ℕ) := elemsOf (pG c)

@[expose] def pOrd (c : ℕ) : ℕ := if c = 0 then 32 else 64

@[expose] def vS (c : ℕ) : ℕ := if c = 0 then 144 else 204

@[expose] def wS (c : ℕ) : ℕ × ℕ := if c = 0 then (112, 224) else (68, 136)

@[expose] def xsS (c : ℕ) : List ℕ :=
  if c = 0 then [2, 1, 19, 50, 7, 14, 233, 151] else [3, 2, 17, 51, 7, 14, 153, 119]

@[expose] def cxs (c : ℕ) (x : List ℕ) : List (List ℕ) :=
  let h : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
  (pE c).filter fun y => h.contains y && mul8 y x == mul8 x y

@[expose] def wE (c : ℕ) : List (List ℕ) := elemsOf (cxs c (xsS c) ++ [xsS c])

@[expose] def mRep (c : ℕ) : List ℕ :=
  if c = 0 then [1, 3, 18, 49, 7, 14, 121, 231] else [1, 3, 12, 8, 35, 18, 72, 196]

@[expose] def mE (c : ℕ) : List (List ℕ) := elemsOf (pG c ++ [mRep c])

@[expose] def oME (c : ℕ) : List (List ℕ) := elemsOf (oddOf (mE c))

@[expose] def kS (c : ℕ) : List ℕ :=
  if c = 0 then [1, 2, 5, 10, 18, 35, 90, 175] else [1, 2, 5, 10, 19, 33, 95, 165]

@[expose] def conjL (c : ℕ) : List (List ℕ × List ℕ × List ℕ) :=
  if c = 0 then
    [([200, 76, 182, 219, 140, 196, 107, 189], [233, 126, 50, 19, 158, 231, 35, 49],
        [76, 200, 4, 12, 151, 126, 9, 7]),
      ([200, 76, 182, 219, 140, 196, 107, 189], [233, 126, 50, 19, 158, 231, 35, 49],
        [85, 255, 90, 245, 119, 238, 121, 231]),
      ([19, 33, 233, 126, 2, 3, 7, 9], [48, 16, 96, 176, 33, 50, 219, 109],
        [2, 1, 19, 50, 7, 14, 233, 151]),
      ([4, 8, 6, 11, 200, 76, 219, 109], [15, 5, 1, 2, 90, 175, 35, 49],
        [2, 1, 19, 50, 7, 14, 233, 151])]
  else
    [([200, 76, 182, 219, 140, 196, 107, 189], [233, 126, 50, 19, 158, 231, 35, 49],
        [90, 245, 85, 255, 214, 189, 221, 187]),
      ([200, 76, 182, 219, 140, 196, 107, 189], [233, 126, 50, 19, 158, 231, 35, 49],
        [109, 219, 221, 187, 165, 95, 85, 255]),
      ([19, 33, 233, 126, 2, 3, 7, 9], [48, 16, 96, 176, 33, 50, 219, 109],
        [3, 2, 17, 51, 7, 14, 153, 119]),
      ([19, 33, 233, 126, 2, 3, 7, 9], [48, 16, 96, 176, 33, 50, 219, 109],
        [90, 245, 85, 255, 214, 189, 221, 187])]

@[expose] def fullImgB (x : List ℕ) : Bool :=
  let S := spanN (imgBasis x)
  S.length == 16 && decide ((S.mergeSort).IsChain (· < ·)) && S.all (fun u => decide (u < 256)) &&
    ((List.range 256).all fun n => S.contains (mv8 x n ^^^ n)) &&
    (S.all fun u => (List.range 256).any fun n => mv8 x n ^^^ n == u) &&
    ((List.range 256).all fun u => !(mv8 x u == u) || S.contains u) &&
    S.all fun u => !(quadN u)

@[expose] def pB (c : ℕ) : Bool :=
  let hG : Std.HashSet (List ℕ) := Std.HashSet.ofList (gamE c)
  subB (pG c) (pE c) && (pE c).length == pOrd c && (pG c).all hG.contains &&
    (List.range 256).all fun v => !((pG c).all fun g => mv8 g v == v) || v == 0 || v == vS c

@[expose] def wB (c : ℕ) : Bool :=
  let h3 : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
  let hF : Std.HashSet (List ℕ) := Std.HashSet.ofList om3FE
  let hW : Std.HashSet (List ℕ) := Std.HashSet.ofList (wE c)
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList (pE c)
  hP.contains (xsS c) && subB (cxs c (xsS c) ++ [xsS c]) (wE c) && (wE c).length == 8 &&
    ((pE c).all fun x => hF.contains x || !(mul8 x x == one8) || smallImgB x || hW.contains x) &&
    (wE c).all fun w =>
      (h3.contains w && mv8 w (vS c) == vS c && mv8 w (wS c).1 == (wS c).1) ||
      (!(hF.contains w) && fullImgB w &&
        (let E := elemsOf (cxs c w ++ [w])
         subB (cxs c w ++ [w]) E && E.length == 8 && E.all hW.contains))

@[expose] def invB (c : ℕ) : Bool :=
  (gamE c).all fun x => x == one8 || !(mul8 x x == one8) ||
    (List.range 256).any fun w => !(b5N w (vS c)) && !([0, vS c].contains (mv8 x w ^^^ w))

@[expose] def ovB (c : ℕ) : Bool :=
  let hG : Std.HashSet (List ℕ) := Std.HashSet.ofList (gamE c)
  let hM : Std.HashSet (List ℕ) := Std.HashSet.ofList (mE c)
  let good : Std.HashSet ℕ := Std.HashSet.ofList ((List.range 256).filter fun u =>
    (pE c).any fun p₁ => mv8 p₁ u != u && (pE c).any fun p₂ =>
      mv8 p₂ u != u && mv8 p₂ u != mv8 p₁ u)
  let w := wS c
  hG.contains (mRep c) && subB (pG c ++ [mRep c]) (mE c) && (mE c).length == 3 * pOrd c &&
    ((gamE c).all fun y => mv8 y (vS c) == vS c || good.contains (mv8 y (vS c)) ||
      hM.contains y ||
      (let B := elemsOf (pG c ++ [y]) (3 * pOrd c + 1)
       decide (3 * pOrd c < B.length) && nodupB B)) &&
    subB (oddOf (mE c)) (oME c) &&
    ((oME c).all fun y => [0, w.1, w.2].contains (mv8 y (vS c) ^^^ vS c)) &&
    ((oME c).any fun y => mv8 y (vS c) ^^^ vS c == w.1) &&
    ((oME c).any fun y => mv8 y (vS c) ^^^ vS c == w.2) && w.1 ^^^ w.2 == vS c

@[expose] def kB (c : ℕ) : Bool :=
  let h3 : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
  let hW : Std.HashSet (List ℕ) := Std.HashSet.ofList (wE c)
  let cg := (conjL c).map fun t => mul8 (mul8 t.1 t.2.2) t.2.1
  let N := elemsOf cg
  let hN : Std.HashSet (List ℕ) := Std.HashSet.ofList N
  h3.contains (kS c) && mul8 (kS c) (kS c) == one8 && !(b5N (mv8 (kS c) (vS c)) (vS c)) &&
    b5N (mv8 (kS c) (vS c)) (wS c).1 &&
    ((conjL c).all fun t => h3.contains t.1 && mul8 t.1 t.2.1 == one8 && hW.contains t.2.2) &&
    subB cg N && om3E.all hN.contains

@[expose] def cenB (c : ℕ) : Bool :=
  let h3 : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
  (wE c).all fun i => h3.contains i ||
    (let C := (gamE c).filter fun x => mul8 x i == mul8 i x
     let Ag := C.filter fun x => pow8 x 15 == one8
     let A := elemsOf Ag
     subB Ag A && A.length == 60 &&
       C.all fun x => x == one8 || x == i || !(pow8 x 16 == one8) ||
         Ag.any fun a =>
           let cm := mul8 (mul8 (pow8 x 15) (pow8 a 14)) (mul8 x a)
           pow8 cm 15 == one8 && !(cm == one8))

@[expose] def o3Check : Bool :=
  basicB && h1B && [0, 1].all fun c => pB c && wB c && invB c && ovB c && kB c && cenB c

end CFSG.Quasithin.H13.O3Cert
