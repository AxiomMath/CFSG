module

public import Certificates.Data.NT44Model.Inputs
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.GH74.GLS.NT44.PermutationNative

open CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

@[expose] def rowOK (n : Nat) (row : Array Nat) : Bool :=
  row.size == n && allLt n fun i => row[i]! < n

@[expose] def rowsOK (n count : Nat) (rows : Array (Array Nat)) : Bool :=
  rows.size == count && allLt count fun i => rowOK n rows[i]!

@[expose] def distinctValues (a : Array Nat) : Bool :=
  allLt a.size fun i => allLt i fun j => a[i]! != a[j]!

@[expose] def wordsLettersOK (j : Nat) (ws : Array (List Int)) : Bool :=
  allLt ws.size fun i => lettersOK j ws[i]!

@[expose] def positiveWordsOK (ws : Array (List Int)) : Bool :=
  allLt ws.size fun i => ws[i]!.all fun l => l == 1 || l == 2 || l == 3 || l == 4

@[expose] def normalizerShapeOK (D : NT44Inputs) : Bool :=
  D.ag.size == 4 && D.ag[0]! == 1 && D.ag[1]! == 2 && D.ag[2]! == 3 &&
    D.ag[3]! == 4 && D.nw.size == 4 &&
    allLt 4 fun k =>
      D.nw[k]!.liftIndex == D.ag[k]! && D.nw[k]!.left.size == 2 &&
        D.nw[k]!.inverse.size == 2 && wordsLettersOK 2 D.nw[k]!.left &&
        wordsLettersOK 2 D.nw[k]!.inverse

@[expose] def shapeOK (D : NT44Inputs) : Bool :=
  D.ks.size == 2 && D.p0.size == 9 && D.lifts.size == 256 &&
    rowsOK 2688 2 D.ks && rowsOK 2688 9 D.p0 && rowsOK 2688 256 D.lifts &&
    D.pts.size == 448 && allLt 448 (fun i => D.pts[i]! < 2688) &&
    distinctValues D.pts &&
    D.sk.size == 7 && D.sp.size == 10 && rowsOK 448 7 D.sk && rowsOK 448 10 D.sp &&
    D.bk.size == 4 && allLt 4 (fun i => D.bk[i]! < 448) && distinctValues D.bk &&
    D.bp.size == 3 && allLt 3 (fun i => D.bp[i]! < 448) && distinctValues D.bp &&
    normalizerShapeOK D &&
    D.tr.size == 256 &&
    allLt 256 (fun i => D.tr[i]!.size == 4 && allLt 4 fun k => D.tr[i]![k]! < 256) &&
    D.inn.size == 9 && allLt 9 (fun i => D.inn[i]! < 256) &&
    D.parent.size == 256 && positiveWordsOK D.parent &&
    D.fwd.size == 2 && D.fwd[0]!.length == 17 && D.fwd[1]!.length == 29 &&
    wordsLettersOK 2 D.fwd &&
    D.rev.size == 2 && D.rev[0]!.length == 45 && D.rev[1]!.length == 36 &&
    wordsLettersOK 2 D.rev &&
    D.wk.size == 7 && D.wp.size == 10 &&
    D.pw.size == 9 && wordsLettersOK 2 D.pw &&
    D.sep.size == 2 && D.sep[0]!.size == 2 && D.sep[0]![0]! == 0 &&
    D.sep[0]![1]! == 0 && D.sep[1]!.size == 2 && D.sep[1]![0]! == 0 &&
    D.sep[1]![1]! == 217

@[expose] def coverCheck (rels : List (List Int)) (z : List Int) (D : NT44Inputs)
    (V VI : Array (Array Nat)) (I : Array Nat) : Bool :=
  allLt 2 (fun i => isInvA 2688 V[i]! VI[i]!) &&
    rels.all (fun w => lettersOK 2 w && eqA 2688 (wordA 2688 V VI w) I) &&
    lettersOK 2 z && eqA 2688 (wordA 2688 V VI z) I &&
    allLt 2 (fun i => lettersOK 2 D.rev[i]! &&
      eqA 2688 (wordA 2688 V VI D.rev[i]!) D.ks[i]!)

@[expose] def restrictionCheck (D : NT44Inputs) (OK OP : Array (Array Nat))
    (KI : Array (Array Nat)) : Bool :=
  allLt 2 (fun i => allLt 448 fun x =>
    D.pts[OK[i]![x]!]! == D.ks[i]![D.pts[x]!]!) &&
    allLt 9 (fun i => allLt 448 fun x =>
      D.pts[OP[i]![x]!]! == D.p0[i]![D.pts[x]!]!) &&
    rawChainOK 448 OK D.sk D.bk D.wk 8 &&
    (rawOrbitSizes 448 D.sk D.bk).prod == 322560 &&
    rawChainOK 448 OP D.sp D.bp D.wp 8 &&
    (rawOrbitSizes 448 D.sp D.bp).prod == 1024 &&
    allLt 9 (fun i => lettersOK 2 D.pw[i]! &&
      eqA 2688 (wordA 2688 D.ks KI D.pw[i]!) D.p0[i]!)

@[expose] def normalizerCheck (D : NT44Inputs) (KI B BI : Array (Array Nat)) : Bool :=
  allLt 4 fun k => allLt 2 fun j =>
    eqA 2688 (wordA 2688 D.ks KI D.nw[k]!.left[j]!)
        (compA 2688 (compA 2688 B[k]! D.ks[j]!) BI[k]!) &&
      eqA 2688 (wordA 2688 D.ks KI D.nw[k]!.inverse[j]!)
        (compA 2688 (compA 2688 BI[k]! D.ks[j]!) B[k]!)

@[expose] def parentCheck (D : NT44Inputs) (LI : Array (Array Nat))
    (U UI : Array (Array Nat)) : Bool :=
  allLt 256 fun i => allLt 2 fun j =>
    eqA 2688 (compA 2688 (compA 2688 D.lifts[i]! D.ks[j]!) LI[i]!)
      (compA 2688 (compA 2688 U[i]! D.ks[j]!) UI[i]!)

@[expose] def transitionCheck (D : NT44Inputs) (LI : Array (Array Nat))
    (sig : Array (Array (Array Nat))) : Bool :=
  allLt 2 (fun j => eqA 2688 sig[0]![j]! D.ks[j]!) &&
    allLt 256 (fun i => allLt 4 fun k => allLt 2 fun j =>
      eqA 2688 sig[D.tr[i]![k]!]![j]!
        (compA 2688 (compA 2688 D.lifts[i]! sig[D.ag[k]!]![j]!) LI[i]!)) &&
    allLt 256 (fun i => allLt 256 fun j =>
      !(decide (i < j)) || sig[i]![0]![0]! != sig[j]![0]![0]! ||
        sig[i]![0]![217]! != sig[j]![0]![217]!)

@[expose] def innerCheck (D : NT44Inputs) (PI : Array (Array Nat))
    (sig : Array (Array (Array Nat))) : Bool :=
  allLt 9 fun i => allLt 2 fun j =>
    eqA 2688 (compA 2688 (compA 2688 D.p0[i]! D.ks[j]!) PI[i]!) sig[D.inn[i]!]![j]!

@[expose] def bridgeCheck (rels : List (List Int)) (z : List Int) : Bool :=
  let D := inputs ()
  if shapeOK D then
    let I := idA 2688
    let KI := D.ks.map (invCand 2688)
    let PI := D.p0.map (invCand 2688)
    let LI := D.lifts.map (invCand 2688)
    let B := D.ag.map fun i => D.lifts[i]!
    let BI := D.ag.map fun i => LI[i]!
    let V := D.fwd.map fun w => wordA 2688 D.ks KI w
    let VI := V.map (invCand 2688)
    let OK := D.sk.extract 0 2
    let OP := D.sp.extract 0 9
    let U := D.parent.map fun w => wordA 2688 B BI w
    let UI := D.parent.map fun w => wordA 2688 B BI (w.reverse.map fun l => -l)
    let sig : Array (Array (Array Nat)) := Array.ofFn (n := 256) fun i =>
      Array.ofFn (n := 2) fun j =>
        compA 2688 (compA 2688 D.lifts[i.val]! D.ks[j.val]!) LI[i.val]!
    allLt 2 (fun i => isInvA 2688 D.ks[i]! KI[i]!) &&
      allLt 9 (fun i => isInvA 2688 D.p0[i]! PI[i]!) &&
      allLt 256 (fun i => isInvA 2688 D.lifts[i]! LI[i]!) &&
      coverCheck rels z D V VI I &&
      restrictionCheck D OK OP KI &&
      normalizerCheck D KI B BI &&
      parentCheck D LI U UI &&
      transitionCheck D LI sig &&
      innerCheck D PI sig
  else
    false

end CFSG.GH74.GLS.NT44.PermutationNative

