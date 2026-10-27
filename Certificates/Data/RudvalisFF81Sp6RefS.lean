module

public import Certificates.Data.RudvalisFF81Sp6Transv

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

@[expose] def sw01C : List ℕ :=
  [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 1]

@[expose] def c7Gen0 : List ℕ :=
  [1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1,
    0, 1, 0, 1, 1]

@[expose] def c7Gen0Inv : List ℕ :=
  [1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1,
    0, 1, 0, 1, 0]

@[expose] def c7Gen1 : List ℕ :=
  [0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0,
    1, 0, 1, 1, 1]

@[expose] def c7Gen1Inv : List ℕ :=
  [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1,
    0, 0, 1, 1, 1]

@[expose] def r0Gen0 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0,
    1, 1, 0, 0, 0]

@[expose] def r0Gen1 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 1, 1]

@[expose] def r0Gen2 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 1, 0, 1, 0]

@[expose] def r2Gen0 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1]

@[expose] def r2Gen1 : List ℕ :=
  [1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1]

@[expose] def r4Gen0 : List ℕ :=
  [1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1,
    1, 0, 1, 1, 1]

@[expose] def r4Gen1 : List ℕ :=
  [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 0, 0, 1]

@[expose] def nP : List (List ℕ × List ℕ) :=
  [zPair 0, (fl0C, fl0C), (sw01C, sw01C), tPair]

@[expose] def nT : Array (List ℕ) :=
  closureT (nP.map Prod.fst)

@[expose] def l1C : List (List ℕ) :=
  [(zPair 0).1, (zPair 0).2, (zPair 1).1, (zPair 1).2, (zPair 2).1, (zPair 2).2]

@[expose] def c7P : List (List ℕ × List ℕ) :=
  [(c7Gen0, c7Gen0Inv), (c7Gen1, c7Gen1Inv)]

@[expose] def repS : Fin 5 → List ℕ :=
  ![fl2C, fl2C, sw01C, sw01C, sw01C]

@[expose] def repA : Fin 5 → List ℕ :=
  ![vecCode 1 0 0, vecCode 1 1 0, vecCode 0 0 1, vecCode 1 1 0, vecCode 1 1 1]

@[expose] def repGens : Fin 5 → List (List ℕ × List ℕ) :=
  ![centGens 0, centGens 3, centGens 2, centGens 3, c7P]

@[expose] def repRP : Fin 5 → List (List ℕ × List ℕ) :=
  ![[(r0Gen0, r0Gen0), (r0Gen1, r0Gen1), (r0Gen2, r0Gen2)], [(fl2C, fl2C)],
    [(r2Gen0, r2Gen0), (r2Gen1, r2Gen1), (sw01C, sw01C)], [(sw01C, sw01C)],
    [(r4Gen0, inv6 r4Gen0), (r4Gen1, inv6 r4Gen1)]]

@[expose] def repW : Fin 5 → ℕ :=
  ![1, 2, 1, 2, 3]

@[expose] def repN : Fin 5 → ℕ :=
  ![8, 2, 8, 2, 8]

@[expose] def repF (k : Fin 5) : List (List ℕ) :=
  (closureT ((repGens k).map Prod.fst)).toList.filter fun x => commutes6 x (repS k)

@[expose] def repR (k : Fin 5) : Array (List ℕ) :=
  closureT ((repRP k).map Prod.fst)

@[expose] def vecIdx (i : ℕ) : List ℕ :=
  vecCode (i / 9) (i / 3 % 3) (i % 3)

@[expose] def wtIdx (i : ℕ) : ℕ :=
  (if i / 9 = 0 then 0 else 1) + (if i / 3 % 3 = 0 then 0 else 1) + (if i % 3 = 0 then 0 else 1)

@[expose] def notMulIdx (i j : ℕ) : Bool :=
  (List.range 3).all fun c =>
    !(j / 9 == c * (i / 9) % 3 && j / 3 % 3 == c * (i / 3 % 3) % 3 && j % 3 == c * (i % 3) % 3)

@[expose] def pairsChk899107 : Bool :=
  nP.all pairCheck && c7P.all pairCheck && (List.finRange 5).all fun k => (repRP k).all pairCheck

@[expose] def nChk899107 : Bool :=
  closureOK (nP.map Prod.fst) nT 1296

@[expose] def normChk899107 : Bool :=
  let m : Std.HashMap (List (List ℕ)) ℕ := (List.range nT.size).foldl (fun m t =>
    m.insert ((List.finRange 3).map fun i => conj6 (nT.getD t []) (zCode i)) t) {}
  (List.range 6).all fun a => (List.range 6).all fun b => (List.range 6).all fun c =>
    !(decide [a / 2, b / 2, c / 2].Nodup) ||
      match m.get? [l1C.getD a [], l1C.getD b [], l1C.getD c []] with
      | some t => decide (t < nT.size) &&
          mul6 (nT.getD t []) (zCode 0) == mul6 (l1C.getD a []) (nT.getD t []) &&
          mul6 (nT.getD t []) (zCode 1) == mul6 (l1C.getD b []) (nT.getD t []) &&
          mul6 (nT.getD t []) (zCode 2) == mul6 (l1C.getD c []) (nT.getD t [])
      | none => false

@[expose] def c7Chk899107 : Bool :=
  c7P.all (fun cc => commutes6 cc.1 (vecCode 1 1 1)) &&
    closureOK (c7P.map Prod.fst) (closureT (c7P.map Prod.fst)) 648 &&
    orbitOK (orbitTable (vecCode 1 1 1)) 2240

@[expose] def repOK (k : Fin 5) : Bool :=
  let F := repF k
  let R := repR k
  let mR := indexMap R
  (repRP k).all (fun r => commutes6 r.1 (repS k) && commutes6 r.1 (repA k)) &&
    closureOK ((repRP k).map Prod.fst) R (repN k) &&
    F.all (fun f => (repRP k).all fun r => found R mR (conj6 f r.1)) &&
    F.all fun x => found R mR x || !(pow512 x == one6) ||
      F.any fun f => !(pow512 (mul6 x (conj6 f x)) == one6)

@[expose] def repChk899107 : Bool :=
  (List.finRange 5).all repOK

@[expose] def abChk899107 : Bool :=
  [0, 2].all (fun k : Fin 5 =>
    allCheck (fun x => allCheck (fun y => commutes6 x y) (repR k) && mul6 x x == one6) (repR k)) &&
    !(commutes6 r4Gen0 r4Gen1)

@[expose] def lookChk899107 : Bool :=
  let m : Std.HashMap (List ℕ × List ℕ) (ℕ × Fin 5) := (List.range nT.size).foldl (fun m t =>
    (List.finRange 5).foldl (fun m k =>
      m.insert (conj6 (nT.getD t []) (repS k), conj6 (nT.getD t []) (repA k)) (t, k)) m) {}
  allCheck (fun s => !(mul6 s s == one6 && !(s == one6)) ||
    let cm := (List.range 27).map fun i => commutes6 s (vecIdx i)
    (List.range 27).all fun i => (List.range 27).all fun j =>
      i == 0 || !(cm.getD i false && cm.getD j false && notMulIdx i j) ||
        match m.get? (s, vecIdx i) with
        | some tk => decide (tk.1 < nT.size) &&
            mul6 (nT.getD tk.1 []) (repS tk.2) == mul6 s (nT.getD tk.1 []) &&
            mul6 (nT.getD tk.1 []) (repA tk.2) == mul6 (vecIdx i) (nT.getD tk.1 []) &&
            repW tk.2 == wtIdx i
        | none => false) nT

@[expose] def slChk899107 : Bool :=
  found (orbitTable (vecCode 1 1 0)) (indexMap (orbitTable (vecCode 1 1 0))) tCode

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS
