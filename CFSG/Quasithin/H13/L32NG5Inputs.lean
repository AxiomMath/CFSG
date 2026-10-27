module

public import CFSG.Quasithin.H13.L32NS7Inputs
public import CFSG.Quasithin.H13.L32NS8Inputs

public section

namespace CFSG.Quasithin.H13.G5Cert

open Mat8Cert S7Cert S8Cert

@[expose] def q5c : List ℕ := [0, 0, 0, 0, 8, 12, 2, 3]

@[expose] def quadN (v : ℕ) : Bool := dotN v (mv8 q5c v)

@[expose] def b5N (v w : ℕ) : Bool := quadN (v ^^^ w) ^^ quadN v ^^ quadN w

@[expose] def gSG : List (List ℕ) :=
  [[1, 2, 4, 8, 17, 34, 68, 136], [16, 32, 64, 128, 1, 2, 4, 8], [1, 2, 5, 10, 16, 32, 80, 160],
    [4, 8, 1, 2, 64, 128, 16, 32], [2, 3, 12, 4, 32, 48, 192, 64],
    [1, 3, 4, 12, 16, 48, 64, 192]]

@[expose] def gAG : List (List ℕ) := gSG.take 5

@[expose] def gSE : List (List ℕ) := elemsOf gSG

@[expose] def gAE : List (List ℕ) := elemsOf gAG

@[expose] def basicB : Bool :=
  subB gSG gSE && gSE.length == 720 && subB gAG gAE && gAE.length == 360

@[expose] def pSG : List (List ℕ) :=
  [[1, 2, 4, 8, 17, 34, 68, 136], [1, 2, 5, 10, 16, 32, 80, 160],
    [1, 2, 6, 11, 16, 32, 96, 176], [1, 3, 4, 12, 16, 48, 64, 192]]

@[expose] def pAG : List (List ℕ) := pSG.take 3

@[expose] def vS : ℕ := 1

@[expose] def pB : Bool :=
  let hS : Std.HashSet (List ℕ) := Std.HashSet.ofList gSE
  let hA : Std.HashSet (List ℕ) := Std.HashSet.ofList gAE
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf pSG)
  let hP' : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf pAG)
  (elemsOf pSG).length == 16 && subB pSG (elemsOf pSG) && pSG.all hS.contains &&
    (elemsOf pAG).length == 8 && subB pAG (elemsOf pAG) && pAG.all hA.contains &&
    (List.range 256).all (fun v => !(pSG.all fun p => mv8 p v == v) || v == 0 || v == vS) &&
    (List.range 256).all (fun v => !(pAG.all fun p => mv8 p v == v) || v < 4) &&
    gSE.all (fun y => !(mv8 y vS == vS) || hP.contains y) &&
    gAE.all fun y => [1, 2, 3].all fun v => !(mv8 y v == v) || hP'.contains y

@[expose] def zPG : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128], [1, 2, 4, 8, 17, 34, 68, 136], [1, 2, 5, 10, 16, 32, 80, 160],
    [1, 2, 5, 10, 17, 34, 85, 170]]

@[expose] def zB : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf pSG)
  zPG.all (fun z => hP.contains z && pSG.all fun p => mul8 z p == mul8 p z) &&
    mul8 (pSG.getD 2 one8) (pSG.getD 3 one8) != mul8 (pSG.getD 3 one8) (pSG.getD 2 one8)

@[expose] def eWS : List (List ℕ × ℕ) :=
  [([1, 2, 4, 8, 17, 34, 68, 136], 16), ([1, 2, 4, 8, 17, 34, 68, 136], 32),
    ([1, 2, 4, 8, 17, 34, 68, 136], 64), ([1, 2, 5, 10, 16, 32, 80, 160], 64)]

@[expose] def eSpanS : List ℕ := spanN (eWS.map fun p => mv8 p.1 p.2 ^^^ p.2)

@[expose] def eWA (v : ℕ) : List (List ℕ × ℕ) :=
  let w := if v = 1 then 64 else if v = 2 then 192 else 128
  [([1, 2, 4, 8, 17, 34, 68, 136], 16), ([1, 2, 4, 8, 17, 34, 68, 136], 32),
    ([1, 2, 4, 8, 17, 34, 68, 136], w), ([1, 2, 5, 10, 16, 32, 80, 160], w),
    ([1, 2, 6, 11, 16, 32, 96, 176], w)]

@[expose] def eSpanA (v : ℕ) : List ℕ := spanN ((eWA v).map fun p => mv8 p.1 p.2 ^^^ p.2)

@[expose] def wB : Bool :=
  let hZ : Std.HashSet (List ℕ) := Std.HashSet.ofList zPG
  let hP' : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf pAG)
  eWS.all (fun p => hZ.contains p.1 && !(b5N p.2 vS)) &&
    [1, 2, 3].all fun v => (eWA v).all (fun p => hP'.contains p.1 && !(b5N p.2 v)) &&
      (eSpanA v).length == 32 && nodupN (eSpanA v)

@[expose] def mRepsS : List (List ℕ) :=
  [[16, 32, 96, 176, 17, 34, 102, 187], [3, 1, 8, 12, 51, 17, 136, 204]]

@[expose] def mES (i : ℕ) : List (List ℕ) := elemsOf (pSG ++ [mRepsS.getD i one8])

@[expose] def ovB : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf pSG)
  let hM : List (Std.HashSet (List ℕ)) := [0, 1].map fun i => Std.HashSet.ofList (mES i)
  let hS : Std.HashSet (List ℕ) := Std.HashSet.ofList gSE
  mRepsS.length == 2 && mRepsS.all hS.contains &&
  ([0, 1].all fun i => (mES i).length == 48 && subB (pSG ++ [mRepsS.getD i one8]) (mES i)) &&
    gSE.all fun y => hP.contains y ||
      (let B := elemsOf (pSG ++ [y]) 49
       (49 ≤ B.length && nodupB B) ||
         (B.length == 48 && nodupB B && hM.any fun h => B.all h.contains))

@[expose] def oES (i : ℕ) : List (List ℕ) := elemsOf (oddOf (mES i))

@[expose] def oWsS : List (ℕ × ℕ) := [(16, 17), (2, 3)]

@[expose] def oB : Bool :=
  [0, 1].all fun i =>
    let w := oWsS.getD i (0, 0)
    let O := oES i
    let R := twoOf O
    let hR : Std.HashSet (List ℕ) := Std.HashSet.ofList R
    w.1 != 0 && w.2 != 0 && w.1 != w.2 &&
      O.all (fun y => [0, w.1, w.2, w.1 ^^^ w.2].contains (mv8 y vS ^^^ vS)) &&
      O.any (fun y => mv8 y vS ^^^ vS == w.1) &&
      O.any (fun y => mv8 y vS ^^^ vS == w.2) &&
      [w.1, w.2, w.1 ^^^ w.2].all eSpanS.contains &&
      O.any (fun y => (List.range 256).any fun v => b5N (mv8 y v ^^^ v) w.1) &&
      subB (oddOf (mES i)) O && nodupB R && O.length == 3 * R.length &&
      R.all (fun a => R.all fun b => hR.contains (mul8 a b)) &&
      O.all fun o => !(pow4 (pow4 o) == one8) || pow4 o == one8

@[expose] def m12ES : List (List ℕ) :=
  elemsOf (pSG ++ [mRepsS.getD 0 one8, mRepsS.getD 1 one8])

@[expose] def blkSA : List (List ℕ) := [[1, 2, 3], [16, 32, 48], [17, 34, 51]]

@[expose] def blkSB : List (List ℕ) := [[1, 16, 17], [2, 32, 34], [3, 48, 51]]

@[expose] def m12B : Bool :=
  subB (pSG ++ [mRepsS.getD 0 one8, mRepsS.getD 1 one8]) m12ES &&
    m12ES.all (fun x => perm3L.contains (blkPerm blkSA x) && perm3L.contains (blkPerm blkSB x)) &&
    m12ES.all (fun x => m12ES.all fun y =>
      blkPerm blkSA (mul8 x y) == compL (blkPerm blkSA x) (blkPerm blkSA y) &&
        blkPerm blkSB (mul8 x y) == compL (blkPerm blkSB x) (blkPerm blkSB y)) &&
    perm3L.all (fun l => perm3L.all fun l' =>
      m12ES.any fun x => blkPerm blkSA x == l && blkPerm blkSB x == l') &&
    m12ES.all fun x => !(blkPerm blkSA x == [0, 1, 2] && blkPerm blkSB x == [0, 1, 2]) ||
      mul8 x x == one8

@[expose] def g5Check : Bool := basicB && pB && zB && wB && ovB && oB && m12B

end CFSG.Quasithin.H13.G5Cert
