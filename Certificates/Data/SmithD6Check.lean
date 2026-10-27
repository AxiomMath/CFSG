module

public import Certificates.Data.SmithD6Model

public noncomputable section

namespace CFSG.SmithD6

@[expose] def chkLineKeys : Bool :=
  lineKeys.size == 365211 &&
  (List.range 365211).all fun k =>
    let p := linePair k
    decide (0 < p.1) && decide (p.1 < p.2) && decide (p.2 < (p.1 ^^^ p.2)) &&
      decide ((p.1 ^^^ p.2) < 4096) && !qf p.1 && !qf p.2 && !bf p.1 p.2 && lineIdx p.1 p.2 == k

@[expose] def chkLineComplete : Bool :=
  singArr.all fun a => singArr.all fun b =>
    a == b || bf a b || decide (lineIdx3 a b (a ^^^ b) < 365211)

@[expose] def matEdge (g p v : Nat) : Bool :=
  let G := tvCols g
  let P := tvCols p
  let V := tvCols v
  (List.range 32).all fun c => applyCols V G[c]! == applyCols G P[c]!

@[expose] def chkLineTree : Bool :=
  gensArr.size == 13 && gensArr[0]! == 0 && gensArr.all (· < 365211) &&
  treeOK 365211 13 (fun v => v == 0)
    (fun g p v => tvImg gensArr[g]! p == v && matEdge gensArr[g]! p v)
    (treeBFS 365211 (Array.range 13) (fun g v => tvImg gensArr[g]! v) [0])

@[expose] def chkWt : Bool :=
  wtArr.size == 75735 && pbArr.size == 75735 && ppArr.size == 75735 && wtArr[0]! == 1 &&
  (List.range 75735).all (fun i => decide (wtArr[i]! < 4294967296)) &&
  (List.range 75734).all (fun i => decide (wtArr[i]! < wtArr[i + 1]!)) &&
  (List.range 75735).all fun i => wtIdx wtArr[i]! == i

@[expose] def chkPlanes : Bool :=
  pbArr[0]! == fBasis &&
  (List.range 75735).all fun i =>
    let B := pbArr[i]!
    let P := ppArr[i]!
    B.size == 6 && P.size == 6 && B.all (· < 4096) &&
      (List.range 64).all fun d => (d == 0 || xorComb B d != 0) && memR B P (xorComb B d)

@[expose] def chkBase (b : Nat) : Bool :=
  let G := tvCols gensArr[b]!
  let p := linePair gensArr[b]!
  (List.range 32).all (fun c => applyCols G G[c]! == 2 ^ c) &&
  (List.range 32).all (fun a => (List.range 32).all fun c =>
    fB G[a]! G[c]! == fB (2 ^ a) (2 ^ c)) &&
  (List.range 75735).all fun i =>
    let j := planeImgM G i
    decide (j < 75735) &&
      (List.range 6).all fun m =>
        memR pbArr[j]! ppArr[j]! (sgl p.1 p.2 pbArr[i]![m]!) &&
          memR pbArr[i]! ppArr[i]! (sgl p.1 p.2 pbArr[j]![m]!)

@[expose] def chkBases : Bool := (List.range 13).all chkBase

@[expose] def oppB (B : Array Nat) : Bool :=
  (List.range 63).all fun e => xorComb B (e + 1) &&& 63 != 0

@[expose] def chkGramRow : Bool :=
  (List.range 75735).all fun j => fB wtArr[0]! wtArr[j]! == oppB pbArr[j]!

@[expose] def chkPlaneTree : Bool :=
  treeOK 75735 13 (fun i => i == 0)
    (fun g p v => planeImgM (tvCols gensArr[g]!) p == v)
    (treeBFS 75735 (Array.range 13) (fun g i => planeImgM gensCols[g]! i) [0])

@[expose] def chkSplit : Bool :=
  singArr.all fun p => (List.range 4096).all fun w =>
    bf p w || !qf w || singArr.any fun s => !bf p s && bf w s

end CFSG.SmithD6
