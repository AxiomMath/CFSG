module

public import CFSG.Quasithin.H13.L32NMat8Inputs

public section

namespace CFSG.Quasithin.H13.S7Cert

open Mat8Cert

@[expose] def s7G : List (List ℕ) :=
  [[1, 9, 12, 14, 208, 192, 96, 32], [10, 5, 9, 13, 32, 176, 80, 240],
    [128, 16, 208, 224, 12, 7, 6, 2]]

@[expose] def s7E : List (List ℕ) := elemsOf s7G

@[expose] def s7BasicB : Bool := subB s7G s7E && s7E.length == 5040

@[expose] def pG : List (List ℕ) :=
  [[5, 10, 4, 8, 16, 32, 80, 160], [9, 14, 4, 8, 16, 32, 96, 176],
    [3, 2, 12, 8, 16, 48, 64, 192], [128, 64, 32, 16, 8, 4, 2, 1]]

@[expose] def vStar : ℕ := 24

@[expose] def pB : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList s7E
  (elemsOf pG).length == 16 && subB pG (elemsOf pG) && pG.all hs.contains &&
    (List.range 256).all fun v => !(pG.all fun p => mv8 p v == v) || v == 0 || v == vStar

@[expose] def n8G : List (List ℕ) :=
  [[5, 10, 4, 8, 16, 32, 80, 160], [3, 2, 12, 8, 16, 48, 64, 192],
    [128, 64, 32, 16, 8, 4, 2, 1]]

@[expose] def cvE : List (List ℕ) := s7E.filter fun x => mv8 x vStar == vStar

@[expose] def invCv (n : List ℕ) : List ℕ :=
  (cvE.find? fun m => mul8 m n == one8).getD one8

@[expose] def cvB : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf n8G)
  let h7 : Std.HashSet (List ℕ) := Std.HashSet.ofList s7E
  (elemsOf n8G).length == 8 && subB n8G (elemsOf n8G) && n8G.all h7.contains &&
    cvE.all (fun n => mul8 (invCv n) n == one8) &&
    cvE.all fun x =>
      !(mul8 x x == one8 && cvE.all fun n =>
          let c := mul8 (mul8 n x) (invCv n)
          mul8 x c == mul8 c x) || hs.contains x

@[expose] def eW : List (List ℕ × ℕ) :=
  [([5, 10, 4, 8, 16, 32, 80, 160], 2), ([5, 10, 4, 8, 16, 32, 80, 160], 64),
    ([5, 10, 4, 8, 16, 32, 80, 160], 129), ([3, 2, 12, 8, 16, 48, 64, 192], 129)]

@[expose] def eSpan : List ℕ := spanN (eW.map fun p => mv8 p.1 p.2 ^^^ p.2)

@[expose] def eWB : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf n8G)
  eW.all fun p => hs.contains p.1 && !(b4N p.2 vStar)

@[expose] def mReps : List (List ℕ) :=
  [[9, 4, 2, 8, 16, 64, 32, 144], [9, 7, 8, 4, 48, 32, 176, 96],
    [64, 240, 16, 48, 12, 8, 3, 10]]

@[expose] def mE (i : ℕ) : List (List ℕ) := elemsOf (pG ++ [mReps.getD i one8])

@[expose] def ovB : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf pG)
  let hM : List (Std.HashSet (List ℕ)) := [0, 1, 2].map fun i => Std.HashSet.ofList (mE i)
  let h7 : Std.HashSet (List ℕ) := Std.HashSet.ofList s7E
  mReps.length == 3 && mReps.all h7.contains &&
  ([0, 1, 2].all fun i => (mE i).length == 48 && subB (pG ++ [mReps.getD i one8]) (mE i)) &&
    s7E.all fun y => hP.contains y ||
      (let B := elemsOf (pG ++ [y]) 49
       (49 ≤ B.length && nodupB B) ||
         (B.length == 48 && nodupB B && hM.any fun h => B.all h.contains))

@[expose] def oddOf (M : List (List ℕ)) : List (List ℕ) :=
  M.filter fun x => mul8 x (mul8 x x) == one8

@[expose] def pow4 (x : List ℕ) : List ℕ := mul8 (mul8 x x) (mul8 x x)

@[expose] def twoOf (O : List (List ℕ)) : List (List ℕ) := O.filter fun x => pow4 x == one8

@[expose] def oE (i : ℕ) : List (List ℕ) := elemsOf (oddOf (mE i))

@[expose] def oWs : List (ℕ × ℕ) := [(0, 0), (44, 52), (36, 60)]

@[expose] def oB : Bool :=
  (mE 0).all (fun y => mv8 y vStar == vStar) &&
    [1, 2].all fun i =>
      let w := oWs.getD i (0, 0)
      let O := oE i
      let R := twoOf O
      let hR : Std.HashSet (List ℕ) := Std.HashSet.ofList R
      w.1 != 0 && w.2 != 0 && w.1 != w.2 &&
        O.all (fun y => [0, w.1, w.2, w.1 ^^^ w.2].contains (mv8 y vStar ^^^ vStar)) &&
        O.any (fun y => mv8 y vStar ^^^ vStar == w.1) &&
        O.any (fun y => mv8 y vStar ^^^ vStar == w.2) &&
        [w.1, w.2, w.1 ^^^ w.2].all eSpan.contains &&
        O.any (fun y => (List.range 256).any fun v => b4N (mv8 y v ^^^ v) w.1) &&
        subB (oddOf (mE i)) O && nodupB R && O.length == 3 * R.length &&
        R.all (fun a => R.all fun b => hR.contains (mul8 a b)) &&
        O.all fun o => !(pow4 (pow4 o) == one8) || pow4 o == one8

@[expose] def m12E : List (List ℕ) := elemsOf (pG ++ [mReps.getD 1 one8, mReps.getD 2 one8])

@[expose] def blkA : List (List ℕ) := [[28, 36, 56], [24, 44, 52], [20, 40, 60]]

@[expose] def blkB : List (List ℕ) := [[28, 40, 52], [24, 36, 60], [20, 44, 56]]

@[expose] def blkIdx (blks : List (List ℕ)) (v : ℕ) : ℕ := blks.findIdx fun b => b.contains v

@[expose] def blkPerm (blks : List (List ℕ)) (x : List ℕ) : List ℕ :=
  blks.map fun b => blkIdx blks (mv8 x (b.getD 0 0))

@[expose] def perm3L : List (List ℕ) :=
  [[0, 1, 2], [1, 0, 2], [0, 2, 1], [2, 1, 0], [1, 2, 0], [2, 0, 1]]

@[expose] def compL (l l' : List ℕ) : List ℕ := l'.map fun j => l.getD j 0

@[expose] def m12B : Bool :=
  subB (pG ++ [mReps.getD 1 one8, mReps.getD 2 one8]) m12E &&
    m12E.all (fun x => perm3L.contains (blkPerm blkA x) && perm3L.contains (blkPerm blkB x)) &&
    m12E.all (fun x => m12E.all fun y =>
      blkPerm blkA (mul8 x y) == compL (blkPerm blkA x) (blkPerm blkA y) &&
        blkPerm blkB (mul8 x y) == compL (blkPerm blkB x) (blkPerm blkB y)) &&
    perm3L.all (fun l => perm3L.all fun l' =>
      m12E.any fun x => blkPerm blkA x == l && blkPerm blkB x == l') &&
    m12E.all fun x => !(blkPerm blkA x == [0, 1, 2] && blkPerm blkB x == [0, 1, 2]) ||
      mul8 x x == one8

@[expose] def s7Check : Bool := s7BasicB && pB && cvB && eWB && ovB && oB && m12B

end CFSG.Quasithin.H13.S7Cert
