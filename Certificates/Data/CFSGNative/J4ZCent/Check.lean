module

public import Certificates.Data.CFSGNative.J4.F2
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.J4.ZCent

open CFSG.Sporadic.J4.Native

instance : Hashable V2 := ⟨V2.hash⟩

@[expose] def wfR (X : Array V2) : Bool := X.size == 112 && X.all V2.wf

@[expose] def mulT (X T : Array V2) : Array V2 := X.map (frApply T)

@[expose] def invW (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def commW (x y : List Int) : List Int := x ++ y ++ invW x ++ invW y

@[expose] def wordT (t ti : Array (Array V2)) (w : List Int) : Array V2 :=
  w.foldl (fun (acc : Array V2) (l : Int) =>
    mulT acc (if 0 < l then t[l.toNat - 1]! else ti[(-l).toNat - 1]!)) idRows

@[expose] def g0W : List (List Int) :=
  [[1], [4], [6], [9], [14], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27],
    [16, 16, 16, 16, 16, 16, 18, 16]]

@[expose] def rW : List (List Int) :=
  [[10, 5, 4, 1, -5, 10], [1, 5, 4, 9, 1, -5, 3], [13, 16, -4, 13, 16, 3, 1],
    [16, 13, 9, 4, 16, 1, 13], [13, 16, -4, 16, 7, 6], [16, 10, 1, 15, 16, 3, 2],
    [3, 16, 6, -5, 16, 7, -5], [3, 16, 8, 6, 3, 16], [16, -4, 9, 3, 16, 7, 6],
    [16, 8, 7, 16, 15, 10, 3], [16, 15, 5, 16, 5, 7, 1], [16, 6, -5, 16, 8, -5],
    [16, 7, -4, 1, 8, 16, 13, 2], [16, 8, 4, 1, 7, 16, 13, 2], [15, 11, 9, 6]]

@[expose] def tW : List (List Int) :=
  [[], [-5], [5], [6], [10], [14], [16], [-5, 14], [-5, 15], [-5, 16], [5, 6], [5, 10], [5, 14],
    [5, 16], [7, 16], [11, 16], [14, -5], [15, 16], [16, -5], [16, 5], [16, 6], [16, 10], [16, 14],
    [-5, 12, 16], [-5, 16, 7], [-5, 16, 10], [-5, 16, 14], [5, 16, -5], [5, 16, 8], [5, 16, 10],
    [5, 16, 11], [6, 5, 16], [6, 16, 8], [7, 16, 14], [7, 16, 15], [8, -5, 16], [8, 16, -5],
    [10, 16, 8], [10, 16, 10], [10, 16, 14], [11, 16, -5], [11, 16, 6], [12, 5, 16], [12, 16, 5],
    [12, 16, 11], [14, -5, 16], [14, 16, 15], [15, 16, 5], [16, -5, 14], [16, -5, 15], [16, 5, 10],
    [16, 6, 5], [16, 8, 16], [16, 14, -5], [16, 14, 16], [5, 11, 16, 6], [5, 12, 16, 11],
    [5, 15, 16, 14], [7, 16, 6, 16], [11, 16, 5, 14]]

@[expose] def perfW : List (List (List Int × List Int)) :=
  [[([5, 12, -4, -5, 8, 1], [16, 12, -4, 13, 16, 9])],
    [([4, 16, 14, 1, -5, 4], [1, 5, 14, 4, 16])],
    [([15, 14, 3], [7, 5, 4, 1, -5, 3])],
    [([16, 4, 3, 1, 16], [9, 2, 16, 13, 12, 10])],
    [([7, 1, 10, 16, 11, 1], [15, 1, 12, 16, 10])],
    [([2, -5], [11, 5, 13, 5])],
    [([4, 16, 10, 5, 16, 11], [-5, 16, 12, 1, 14, 16])],
    [([12, 1, -5, 9, -4], [3, 1, -5, -4, 9])],
    [([10, 16, 13, 16, 2], [16, 1, 13, 9, 16, 10])],
    [([9, 1, 5, 6, 1], [-5, 10, 1, 13, -5])],
    [([1, 10, 3, 1], [15, -5, 16, 9, 3, 16])],
    [([14, 12, 7], [1, 10, 5, 4, 14, 1])],
    [([6, 16, 12, 5, 4, 4], [16, 13, -5, 4, 9])],
    [([2, -5, 8, 16, 15, -5], [16, 12, 16, 4, 9, 4]),
      ([13, 16, 12, 1, 13, -5], [5, 16, 9, 6, -4, 11])],
    [([2, -5, 8, 16, 15, -5], [-5, 10, 6, 16, 10, 9]), ([8, 16, 7, 5, 1, 5], [15, 9, 4, 16, 5, 1])],
    [([-5, 12, 1, 16, 3], [10, 7, 4, 5, 16, 1])]]

@[expose] def perfWord (l : List (List Int × List Int)) : List Int :=
  l.flatMap fun p => commW p.1 p.2

@[expose] def rExp (rt : Array (Array V2)) (c : Nat) : Array V2 :=
  (List.range 15).foldl (fun acc j => if c.testBit j then mulT acc rt[j]! else acc) idRows

@[expose] def rsetOf (rt : Array (Array V2)) : Std.HashSet (Array V2) :=
  (List.range 32768).foldl (fun (s : Std.HashSet (Array V2)) (c : Nat) => s.insert (rExp rt c)) ∅

structure Setup where
  gt : Array (Array V2)
  git : Array (Array V2)
  b : Array (Array V2)
  bi : Array (Array V2)
  bt : Array (Array V2)
  bit : Array (Array V2)
  r : Array (Array V2)
  rt : Array (Array V2)
  t : Array (Array V2)
  ti : Array (Array V2)
  rset : Std.HashSet (Array V2)

@[expose] def gtOf (gm : Array (Array V2)) : Array (Array V2) := gm.map frTable

@[expose] def gitOf (gm : Array (Array V2)) : Array (Array V2) := (gm.map invRows).map frTable

@[expose] def bOf (gm : Array (Array V2)) : Array (Array V2) :=
  (g0W.map (wordT (gtOf gm) (gitOf gm))).toArray

@[expose] def biOf (gm : Array (Array V2)) : Array (Array V2) := (bOf gm).map invRows

@[expose] def btOf (gm : Array (Array V2)) : Array (Array V2) := (bOf gm).map frTable

@[expose] def bitOf (gm : Array (Array V2)) : Array (Array V2) := (biOf gm).map frTable

@[expose] def rOf (gm : Array (Array V2)) : Array (Array V2) :=
  (rW.map (wordT (btOf gm) (bitOf gm))).toArray

@[expose] def rtOf (gm : Array (Array V2)) : Array (Array V2) := (rOf gm).map frTable

@[expose] def tOf (gm : Array (Array V2)) : Array (Array V2) :=
  (tW.map (wordT (btOf gm) (bitOf gm))).toArray

@[expose] def tiOf (gm : Array (Array V2)) : Array (Array V2) := (tOf gm).map invRows

@[expose] def setup (gm : Array (Array V2)) : Setup where
  gt := gtOf gm
  git := gitOf gm
  b := bOf gm
  bi := biOf gm
  bt := btOf gm
  bit := bitOf gm
  r := rOf gm
  rt := rtOf gm
  t := tOf gm
  ti := tiOf gm
  rset := rsetOf (rtOf gm)

@[expose] def chkBase (gm : Array (Array V2)) (S : Setup) : Bool :=
  gm.size == 32 && S.b.size == 16 && S.r.size == 15 && S.t.size == 60 &&
    (List.range 32).all (fun n => wfR gm[n]! && eqRows (mulT gm[n]! S.git[n]!) idRows) &&
    (List.range 16).all (fun i => eqRows (mulT S.b[i]! S.bit[i]!) idRows) &&
    (List.range 60).all fun i => eqRows (mulT S.t[i]! (frTable S.ti[i]!)) idRows

@[expose] def chkR (S : Setup) : Bool :=
  S.rset.size == 32768 &&
    (List.range 32768).all fun c =>
      let x := rExp S.rt c
      let xt := frTable x
      (List.range 15).all (fun j => S.rset.contains (mulT x S.rt[j]!)) &&
        ((List.range 15).any (fun j => !eqRows (mulT x S.rt[j]!) (mulT S.r[j]! xt)) ||
          (List.range 16).all fun i => eqRows (mulT x S.bt[i]!) (mulT S.b[i]! xt))

@[expose] def chkNormR (S : Setup) : Bool :=
  (List.range 16).all fun i => (List.range 15).all fun j =>
    S.rset.contains (mulT (mulT S.b[i]! S.rt[j]!) S.bit[i]!)

@[expose] def inTR (S : Setup) (x : Array V2) : Bool :=
  let xt := frTable x
  (List.range 60).any fun i => S.rset.contains (mulT S.ti[i]! xt)

@[expose] def chkCover (S : Setup) : Bool :=
  (List.range 60).all fun i => (List.range 16).all fun j => inTR S (mulT S.t[i]! S.bt[j]!)

@[expose] def chkPerf (S : Setup) : Bool :=
  (List.range 16).all fun i =>
    eqRows (wordT S.bt S.bit (perfWord (perfW.getD i []))) S.b[i]!

@[expose] def cMatZ (gm : Array (Array V2)) (S : Setup) : Array V2 :=
  mulT (mulT (mulT gm[12]! S.gt[13]!) S.git[12]!) S.git[13]!

@[expose] def cInvZ (gm : Array (Array V2)) (S : Setup) : Array V2 :=
  mulT (mulT (mulT gm[13]! S.gt[12]!) S.git[13]!) S.git[12]!

@[expose] def chkK (gm : Array (Array V2)) (S : Setup) : Bool :=
  let c := cMatZ gm S
  let ci := cInvZ gm S
  eqRows (mulT c (frTable ci)) idRows &&
    (List.range 12).all (fun k => (List.range 16).all fun i =>
      inTR S (mulT (mulT gm[k]! S.bt[i]!) S.git[k]!)) &&
    (List.range 16).all fun i => inTR S (mulT (mulT c S.bt[i]!) (frTable ci))

@[expose] def chk9685 (gm : Array (Array V2)) : Bool :=
  let S := setup gm
  chkBase gm S && chkR S && chkNormR S && chkCover S

@[expose] def chk9686 (gm : Array (Array V2)) : Bool :=
  let S := setup gm
  chkBase gm S && chkPerf S && chkK gm S

end CFSG.Sporadic.J4.ZCent
