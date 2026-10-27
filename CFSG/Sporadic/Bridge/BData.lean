module

public import Certificates.Data.CFSGNative.MonsterB.Primes

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

set_option compiler.extract_closed false

@[expose] def sevenProg : List Ins :=
  [
    .pwr 2 2 3, .mu 3 1 4, .mu 3 4 5, .mu 5 5 6, .mu 6 6 6, .mu 6 6 6, .mu 6 6 6, .mu 6 5 6,
    .mu 1 2 7, .mu 7 2 8, .mu 8 8 9, .mu 9 9 9, .mu 9 9 9, .mu 9 9 9, .mu 8 9 9, .mu 3 9 3,
    .mu 6 3 3, .mu 4 4 10, .mu 10 4 10, .mu 10 10 10, .mu 10 10 10, .mu 10 4 10, .mu 5 4 5,
    .mu 5 4 5, .mu 5 5 4, .mu 4 4 5, .mu 5 4 4, .mu 4 5 4, .mu 7 7 5, .mu 7 5 5, .mu 5 5 5,
    .mu 5 5 5, .mu 7 5 5, .mu 4 5 4, .mu 10 4 4, .mu 3 4 4, .mu 3 4 3, .pwr 9 3 11, .pwr 10 4 12,
    .mu 11 12 11, .mu 7 8 12, .mu 7 12 8, .mu 8 8 7, .mu 7 7 12, .mu 7 12 8, .mu 12 8 7,
    .mu 10 7 12, .mu 12 5 8, .mu 6 2 10, .mu 10 9 7, .mu 8 7 12, .pwr 5 12 5, .mu 5 7 6,
    .pwr 5 6 10, .mu 11 10 9, .pwr 10 12 8, .mu 12 7 6, .pwr 9 6 11, .mu 8 11 10, .mu 9 10 8,
    .pwr 3 8 11, .pwr 2 4 9, .pwr 8 3 10, .pwr 5 4 3, .mu 10 3 4, .mu 9 4 10, .mu 10 7 3,
    .pwr 8 6 9, .mu 5 9 4, .pwr 2 12 10, .mu 4 10 7, .mu 3 7 6, .pwr 2 6 5, .mu 11 5 9,
    .mu 9 8 12, .mu 12 8 4, .mu 4 6 10, .mu 10 11 3, .mu 6 8 7, .mu 7 8 9, .mu 9 5 12,
    .mu 12 8 4, .mu 4 8 10]

@[expose] def sevenN : Nat := 13

@[expose] def sevenRx : Nat := 3

@[expose] def sevenRy : Nat := 10

@[noinline, expose] def sevenChecks (R : Array Mat) (flag : Bool) : Bool :=
  let X := R.getD sevenRx #[]
  let Y := R.getD sevenRy #[]
  flag && ordOK 4370 7 X && ordOK 4370 7 Y && (mulP 4370 X Y == mulP 4370 Y X) &&
    (List.range 7).all fun k => neM 4370 Y (powM 4370 X k)

@[expose] def sevenOK : Bool :=
  let st := regRun 4370 sevenN sevenProg (seedMat 4370 CFSG.SectionRank.Native.bData.seedA)
    (seedMat 4370 CFSG.SectionRank.Native.bData.seedB)
  sevenChecks st.1 st.2

@[expose] def bProg : List Ins :=
  [
    .mu 1 2 3, .pwr 15 3 4, .mu 4 2 4, .pwr 19 4 5, .mu 1 5 6, .pwr 3 6 6, .pwr 2 2 7, .mu 7 1 8,
    .pwr 15 8 9, .mu 7 9 7, .pwr 3 7 9, .mu 9 6 9, .pwr 10 9 9, .mu 9 4 9, .mu 7 9 9, .mu 6 9 10,
    .pwr 4 10 11, .pwr 3 4 12, .mu 6 12 12, .pwr 10 12 12, .mu 7 12 12, .mu 12 4 12, .mu 12 6 13,
    .pwr 6 13 14, .mu 14 6 14, .pwr 3 13 15, .mu 14 15 14, .pwr 2 14 14, .mu 14 12 14,
    .mu 14 6 14, .pwr 2 12 12, .mu 14 12 14, .mu 14 6 14, .pwr 5 14 14, .mu 11 14 11,
    .pwr 4 13 14, .mu 11 14 11, .pwr 2 9 14, .mu 14 10 9, .mu 6 9 14, .pwr 2 14 9, .pwr 3 10 14,
    .pwr 8 10 10, .mu 6 10 10, .mu 14 10 14, .mu 13 12 10, .mu 10 6 12, .pwr 2 12 10,
    .mu 14 10 12, .mu 9 12 14, .mu 11 14 12, .mu 12 11 16, .pwr 8 13 13, .mu 13 6 13,
    .mu 13 15 6, .mu 9 6 13, .mu 13 10 15, .mu 15 11 9, .mu 16 9 6, .mu 14 12 13, .mu 13 11 10,
    .mu 9 15 16, .mu 10 16 13, .pwr 2 14 10, .mu 10 12 16, .mu 16 11 10, .pwr 2 15 16,
    .mu 9 16 16, .mu 10 16 10, .pwr 3 14 16, .mu 16 12 16, .mu 16 11 16, .pwr 3 15 17,
    .mu 9 17 17, .mu 16 17 16, .pwr 4 14 17, .mu 17 12 17, .mu 17 11 17, .pwr 4 15 18,
    .mu 9 18 18, .mu 17 18 17, .pwr 5 14 18, .mu 18 12 18, .mu 18 11 18, .pwr 5 15 19,
    .mu 9 19 19, .mu 18 19 18, .pwr 6 14 19, .mu 19 12 14, .mu 14 11 19, .pwr 6 15 12,
    .mu 9 12 14, .mu 19 14 15, .mu 10 13 9, .pwr 5 3 12, .mu 12 5 19, .pwr 5 8 14, .mu 19 14 3,
    .mu 3 11 8, .mu 8 12 19, .mu 5 14 3, .mu 12 3 8, .mu 11 8 12, .mu 14 12 3, .mu 7 3 8,
    .mu 19 8 14, .pwr 2 14 12, .mu 19 4 7, .mu 7 3 8, .pwr 2 8 19, .mu 16 19 4, .mu 12 4 7,
    .mu 13 10 3, .mu 12 16 4, .mu 4 19 12, .mu 3 12 4, .mu 7 4 19, .mu 9 19 4, .pwr 5 14 19,
    .pwr 5 8 14, .mu 16 14 8, .mu 19 8 8, .mu 19 16 19, .mu 19 14 19, .mu 3 19 14, .mu 8 14 14,
    .mu 9 14 14, .mu 14 4 20, .pwr 3 20 21, .mu 14 21 21, .mu 4 21 21, .mu 21 15 22, .mu 7 9 7,
    .mu 7 12 7, .mu 7 3 12, .mu 8 9 7, .mu 7 19 8, .mu 8 3 9, .mu 12 9 7, .pwr 3 7 19,
    .mu 19 9 8, .mu 8 12 3, .mu 22 3 19, .mu 15 3 8, .mu 21 8 22, .mu 18 17 3, .pwr 4 20 21,
    .pwr 4 7 8, .mu 15 8 23, .mu 21 23 23, .mu 17 18 24, .mu 21 15 21, .mu 21 8 21, .mu 24 21 8,
    .mu 23 8 8, .mu 3 8 8, .mu 4 14 4, .mu 9 12 14, .mu 15 14 9, .mu 4 9 12, .mu 4 15 9,
    .mu 9 14 4, .mu 24 4 9, .mu 12 9 14, .mu 3 14 9, .mu 15 7 14, .mu 20 14 14, .mu 20 15 20,
    .mu 20 7 20, .mu 24 20 7, .mu 14 7 7, .mu 3 7 7, .mu 9 7 9, .mu 8 9 7, .mu 22 7 9,
    .pwr 3 9 7, .mu 8 7 9, .mu 22 9 8, .pwr 4 8 7, .mu 7 19 22, .mu 14 3 9, .mu 9 20 7,
    .mu 7 24 14, .mu 12 3 9, .mu 9 4 20, .mu 20 24 7, .mu 14 7 12, .mu 23 3 9, .mu 9 21 4,
    .mu 4 24 20, .mu 12 20 14, .mu 14 19 7, .pwr 3 7 23, .mu 23 20 3, .mu 3 19 9, .pwr 4 9 21,
    .mu 22 21 4, .mu 19 4 24, .mu 8 4 12, .mu 12 9 14, .mu 14 4 7, .mu 7 19 23, .mu 23 4 20,
    .mu 20 14 3, .mu 24 3 22, .mu 22 4 21, .mu 21 19 8]

@[expose] def bN : Nat := 25

@[expose] def bTreg (k : Nat) : Nat := [11, 6, 13, 10, 16, 17, 18, 15, 8, 3, 5].getD k 0

inductive Wd where
  | gen (i : Nat)
  | mul (u v : Wd)
  | pow (u : Wd) (e : Nat)

@[expose] def Wd.evalN (n : Nat) (T : Array Mat) : Wd → Mat
  | .gen i => T.getD i #[]
  | .mul u v => mulP n (u.evalN n T) (v.evalN n T)
  | .pow u e => powM n (u.evalN n T) e

@[expose] def Wd.gensLt (m : Nat) : Wd → Bool
  | .gen i => decide (i < m)
  | .mul u v => u.gensLt m && v.gensLt m
  | .pow u _ => u.gensLt m

@[expose] def Wd.chain (i : Nat) (l : List Nat) : Wd :=
  l.foldl (fun w j => .mul w (.gen j)) (.gen i)

@[expose] def wR : Wd := .chain 0 [1, 2, 3, 4, 5, 6, 7]

@[expose] def wS : Wd := .chain 4 [8, 9, 10]

@[expose] def wRi : Wd := .chain 7 [6, 5, 4, 3, 2, 1, 0]

@[expose] def wSi : Wd := .chain 10 [9, 8, 4]

@[expose] def wA : Wd := .pow (.mul (.pow wR 7) wS) 15

@[expose] def wB : Wd :=
  .mul (.mul (.pow (.mul wRi wSi) 10) (.mul (.gen 0) (.gen 1))) (.pow (.mul wS wR) 10)

@[expose] def wordN (n : Nat) (T : Array Mat) : List (Nat × Bool) → Mat
  | [] => idMat n
  | l :: w => w.foldl (fun acc l' => mulP n acc (T.getD l'.1 #[])) (T.getD l.1 #[])

@[expose] def relFactor (r : List (Nat × Bool)) : List (Nat × Bool) × Nat :=
  match (List.range r.length).find? fun q =>
      r.length % (q + 1) == 0 && r == (List.replicate (r.length / (q + 1)) (r.take (q + 1))).flatten
  with
  | some q => (r.take (q + 1), r.length / (q + 1))
  | none => (r, 1)

@[noinline, expose] def relsOK (T : Array Mat) (rels : List (List (Nat × Bool))) : Bool :=
  rels.all fun r =>
    (relFactor r).1.all (fun l => decide (l.1 < 11)) &&
      r == (List.replicate (relFactor r).2 (relFactor r).1).flatten &&
      powM 4370 (wordN 4370 T (relFactor r).1) (relFactor r).2 == idMat 4370

@[expose] def treeText : String := include_str "BTree.txt"

@[expose] def rowText : String := include_str "BRow0.txt"

@[expose] def treeOfText (s : String) : Array (Nat × Bool) :=
  ((s.splitOn "\n").filterMap fun l =>
    match l.splitOn " " with
    | [p, g] => some (p.toNat?.getD 0, g == "1")
    | _ => none).toArray

@[expose] def rowOfText (s : String) : Row :=
  ((((s.splitOn "\n").headD "").splitOn " ").filterMap String.toNat?).toArray

@[noinline, expose] def spinMat (n : Nat) (v0 : Row) (X Y : Mat) (tree : Array (Nat × Bool)) :
    Mat :=
  tree.foldl (fun S pg => S.push (vecMulC n (S.getD pg.1 #[]) (if pg.2 then Y else X))) #[v0]

@[noinline, expose] def conjChecks (A B a' b' : Mat) : Bool :=
  let tree := treeOfText treeText
  let S := spinMat 4370 (unitRow 4370 0) A B tree
  let S' := spinMat 4370 (rowOfText rowText) a' b' tree
  let Gm := mulP 4370 (invM 4370 S) S'
  let Gi := mulP 4370 (invM 4370 S') S
  mulP 4370 A Gm == mulP 4370 Gm a' && mulP 4370 B Gm == mulP 4370 Gm b' &&
    mulP 4370 Gm Gi == idMat 4370

@[noinline, expose] def bChecks (A B : Mat) (R : Array Mat) (flag : Bool)
    (rels : List (List (Nat × Bool))) : Bool :=
  let T : Array Mat := Array.ofFn (n := 11) fun k => R.getD (bTreg k.1) #[]
  flag && (List.range 11).all (fun k => mulP 4370 (T.getD k #[]) (T.getD k #[]) == idMat 4370) &&
    relsOK T rels &&
    wA.gensLt 11 && wB.gensLt 11 && conjChecks A B (wA.evalN 4370 T) (wB.evalN 4370 T)

@[expose] def bCheck (rels : List (List (Nat × Bool))) : Bool :=
  let A := seedMat 4370 CFSG.SectionRank.Native.bData.seedA
  let B := seedMat 4370 CFSG.SectionRank.Native.bData.seedB
  let st := regRun 4370 bN bProg A B
  bChecks A B st.1 st.2 rels

end CFSG.Sporadic.Bridge.B
