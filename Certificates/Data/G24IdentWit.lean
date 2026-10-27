module

public import Certificates.Data.G24IdentDC
public import Certificates.Data.G24IdentPc

public section

namespace CFSG.Quasithin.St84.G24Wit

open CFSG.Fischer CFSG.LieType.Multipliers.G24 CFSG.Quasithin.St84.G24Ident
  CFSG.Quasithin.St84.G24Pc CFSG.Quasithin.St84.G24DC

@[expose] def e1Q : List (List (Fin 10)) :=
  [[0, 4],
   [1, 5, 8, 9],
   [2, 6, 8, 9],
   [3, 7, 8, 9],
   [4, 9],
   [5],
   [6],
   [7],
   [8, 9],
   [9]]

@[expose] def e1A : List (List (Fin 3 × Bool)) :=
  [[(0, true)], [(1, true)], [(2, false)]]

@[expose] def conjQ1 : List (List (List (Fin 10))) :=
  [[[0, 8],
    [0, 1, 8, 9],
    [0, 3, 8, 9],
    [0, 2, 8, 9],
    [4, 9],
    [4, 5, 8],
    [4, 7, 8],
    [4, 6, 8],
    [8],
    [9]],
   [[3, 9],
    [0, 8, 9],
    [2],
    [1, 8],
    [7, 8, 9],
    [4, 8],
    [6],
    [5, 9],
    [8],
    [9]],
   [[0, 4, 8, 9],
    [1, 5, 8, 9],
    [2, 6, 8, 9],
    [3, 7, 8, 9],
    [0],
    [1],
    [2],
    [3],
    [8, 9],
    [8]]]

@[expose] def dec1 : List (List (Fin 10) × List (Fin 3)) :=
  [([], [2]),
   ([], [1, 1, 0, 1, 0, 1, 1, 0]),
   ([], [1, 0, 1, 0, 1, 1, 0, 1, 0]),
   ([4, 5, 6, 7], [])]

@[expose] def e2Coc : List (List (List (Fin 10))) :=
  [[[], [], []],
   [[7, 9], [6, 7], []],
   [[6, 8], [7], []],
   [[6, 7, 8, 9], [6], []]]

@[expose] def dec2 : List (List (Fin 10) × List (Fin 3)) :=
  [([7, 8, 9], [0, 1, 0, 1, 0, 1, 1, 2]),
   ([], [2]),
   ([0, 2, 7, 8, 9], []),
   ([], [0])]

@[expose] def matsOf (ws : List Word) : Array Mat × Array Mat :=
  ((ws.map wordArr).toArray, (ws.map fun w => wordArr w.reverse).toArray)

@[expose] def invW {n : ℕ} (w : List (Fin n × Bool)) : List (Fin n × Bool) :=
  w.reverse.map fun l => (l.1, !l.2)

@[expose] def evalL {n : ℕ} (G : Array Mat × Array Mat) (w : List (Fin n × Bool)) : Mat :=
  w.foldr (fun l A => mulArr 14 (if l.2 then G.1.getD l.1.val one14 else G.2.getD l.1.val one14) A)
    one14

@[expose] def evalP {n : ℕ} (G : Array Mat) (w : List (Fin n)) : Mat :=
  w.foldr (fun l A => mulArr 14 (G.getD l.val one14) A) one14

@[expose] def evalPInv {n : ℕ} (Gi : Array Mat) (w : List (Fin n)) : Mat :=
  w.foldl (fun A l => mulArr 14 (Gi.getD l.val one14) A) one14

@[expose] def conjArr (g x g' : Mat) : Mat := mulArr 14 (mulArr 14 g x) g'

@[expose] def frobArr (A : Mat) : Mat := A.map fun r => r.map fun x => x * x

@[expose] def cocImgs (P2 A2 : Array Mat × Array Mat) (D : List (List (Fin 10))) :
    Array Mat × Array Mat :=
  (((List.range 3).map fun t => mulArr 14 (evalP P2.1 (D.getD t [])) (A2.1.getD t one14)).toArray,
   ((List.range 3).map fun t =>
      mulArr 14 (A2.2.getD t one14) (evalPInv P2.2 (D.getD t []))).toArray)

@[expose] def witCheck (_ : Unit := ()) : Bool :=
  let P1 := matsOf pc1
  let P2 := matsOf pc2
  let A1 := matsOf [a1, b1, k1]
  let A2 := matsOf [a2, b2, k2]
  let be : Array Mat × Array Mat :=
    ((e1Q.map (evalP P1.1)).toArray, (e1Q.map (evalPInv P1.2)).toArray)
  let al : Array Mat × Array Mat :=
    ((e1A.map (evalL A1)).toArray, (e1A.map fun w => evalL A1 (invW w)).toArray)
  let cs := e2Coc.map (cocImgs P2 A2)
  let w := wImg ()
  relsQ1.all (fun r => decide (evalL be r = one14)) &&
  (List.range 10).all (fun j => decide (evalP be.1 (e1Q.getD j []) = P1.1.getD j one14)) &&
  relsA.all (fun r => decide (evalL al r = one14)) &&
  (List.range 3).all (fun t => (List.range 10).all fun j =>
    decide (conjArr (A1.1.getD t one14) (P1.1.getD j one14) (A1.2.getD t one14) =
      evalP P1.1 ((conjQ1.getD t []).getD j [])) &&
    decide (evalP be.1 ((conjQ1.getD t []).getD j []) =
      conjArr (al.1.getD t one14) (be.1.getD j one14) (al.2.getD t one14))) &&
  (List.range 4).all (fun k =>
    let d := dec1.getD k ([], [])
    decide (gB.getD k one14 = mulArr 14 (evalP P1.1 d.1) (evalP A1.1 d.2)) &&
    decide ((w.getD 2 #[]).getD k one14 = mulArr 14 (evalP be.1 d.1) (evalP al.1 d.2))) &&
  cs.all (fun c => relsA.all fun r => decide (evalL c r = one14)) &&
  e2Coc.all (fun D => D.all fun z => z.all fun l => decide (6 ≤ l.val)) &&
  (List.range 4).all (fun k =>
    let d := dec2.getD k ([], [])
    decide (gB.getD k one14 = mulArr 14 (evalP P2.1 d.1) (evalP A2.1 d.2)) &&
    (List.range 4).all fun s =>
      decide ((w.getD (4 + s) #[]).getD k one14 =
        mulArr 14 (evalP P2.1 d.1) (evalP (cs.getD s (#[], #[])).1 d.2))) &&
  decide (w.getD 0 #[] = gB) &&
  decide (w.getD 1 #[] = gB.map frobArr) &&
  decide (w.getD 3 #[] = (w.getD 2 #[]).map frobArr) &&
  (List.range 4).all (fun s => decide (w.getD (8 + s) #[] = (w.getD (4 + s) #[]).map frobArr)) &&
  wWords.all (fun r => (r.take 2).all fun u => u.all fun l => decide (l.val < 2))

end CFSG.Quasithin.St84.G24Wit
