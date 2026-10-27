module

public import Certificates.Data.CFSGNative.Th.Data
public import Certificates.Data.CFSGNative.Th.Sift
public import Certificates.Data.CFSGNative.Th.Suborbits

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Th.Native

@[expose] def tblA (_ : Unit) : Array V4 := frTable (transposeRows (rowsOf seedA))

@[expose] def tblB (_ : Unit) : Array V4 := frTable (transposeRows (rowsOf seedB))

@[expose] def thBFS (_ : Unit) : BFSState :=
  let st := bfs (tblA ()) (tblB ()) wKey 150000000
  ⟨id st.keys, id st.slots, id st.alpha, id st.beta, id st.par, id st.count⟩

@[expose] def thN (_ : Unit := ()) : Nat := 143127000

@[expose] def q0Size (_ : Unit := ()) : Nat := 11741184

@[expose] def q1Size (_ : Unit := ()) : Nat := 54

@[expose] def suborbitSizes (_ : Unit := ()) : List Nat :=
  [1, 11741184, 5031936, 105670656, 8805888, 8128512, 1304576, 45864, 2201472, 179712, 17199]

@[expose] def deltaOK (st : BFSState) : Bool :=
  allIn 0 124 fun i => (readKey st.keys i).beq (deltaKeys[i]!)

@[inline, expose] def letters (P₁ P₂ : Table) (s : Nat) : Table := if s = 1 then P₁ else P₂

@[inline, expose] def wordLetters (P Q Qi : Table) (l : Int) : Table :=
  if l = 1 ∨ l = -1 then P else if l = 2 then Q else Qi

@[expose] def abPow19 (α β : Table) (p : Nat) : Nat :=
  (List.range 19).foldl (fun q _ => ap α (ap β q)) p

@[expose] def globalChecks (n : Nat) (alpha beta betaInv gpl : Table) (c : Chain) (chunks : Nat) :
    Bool :=
  parAll n chunks (fun i =>
      (!reqTwo gpl (ap alpha) 1 i ||
        globalTest gpl (letters alpha beta) (letters alpha betaInv) c 1 i) &&
      (!reqThree gpl (ap beta) 2 i ||
        globalTest gpl (letters alpha beta) (letters alpha betaInv) c 2 i)) &&
    parAll n chunks (fun i => abPow19 alpha beta i == i)

@[expose] def tableChecks (n : Nat) (alpha beta betaInv gpl : Table) (chunks : Nat) : Bool :=
  let mx := wordT n (wordLetters alpha beta betaInv) xWord
  let my := wordT n (wordLetters alpha beta betaInv) yWord
  if !(invoOK n mx && order3OK n my && ap mx 0 == 0 && ap my 0 == 0) then false else
  let myi := invT n my
  let mz0 := wordT n (wordLetters mx my myi) zWord0
  let mz1 := wordT n (wordLetters mx my myi) zWord1
  let mz0i := invT n mz0
  let mz1i := invT n mz1
  if !(invOK n my myi && invOK n mz0 mz0i && invOK n mz1 mz1i && ap mz0 1 == 1 &&
      ap mz1 1 == 1) then false else
  let q0 := localBFS n 1 mx my
  let pts0 := q0.1
  let pl0 := q0.2.1
  let pos0 := q0.2.2
  let q1 := smallBFS 2 q1Size mz0 mz1
  let pts1 := q1.1
  let pl1 := q1.2
  if !(pts0.size == q0Size && pts1.size == q1Size &&
      treeOK n q0Size 1 pts0 pl0 (ap pos0) mx my &&
      treeOK n q1Size 2 pts1 pl1 (findPt pts1) mz0 mz1) then false else
  let c : Chain := ⟨pl0, pos0, letters mx myi, pts1, pl1, letters mz0i mz1i⟩
  let okTwo := allIn 0 q1Size fun k =>
    levelTwoTest c (letters mz0 mz1) 1 k && levelTwoTest c (letters mz0 mz1) 2 k
  let okOne := parAll q0Size chunks fun k =>
    (!reqTwo pl0 (fun j => ap pos0 (ap mx (ap pts0 j))) 1 k ||
      levelOneTest pts0 c (letters mx my) 1 k) &&
    (!reqThree pl0 (fun j => ap pos0 (ap my (ap pts0 j))) 2 k ||
      levelOneTest pts0 c (letters mx my) 2 k)
  if !(okTwo && okOne) then false else
  let comps := components n mx my
  let okSub := comps.reps.size == 11 && compOK n comps mx my &&
    (countLabels n 11 comps).toList == suborbitSizes
  okSub && globalChecks n alpha beta betaInv gpl c chunks

@[expose] def thCertificate (chunks : Nat) : Bool :=
  let st := thBFS ()
  if !(st.count == thN && orbitOK (tblA ()) (tblB ()) wKey st chunks && deltaOK st) then false
  else
    let n := st.count
    let alpha := tblOfBytes n st.alpha
    let beta := tblOfBytes n st.beta
    let gpl := tblOfBytes n st.par
    let betaInv := invT n beta
    invoOK n alpha && order3OK n beta && invOK n beta betaInv && ap alpha 0 == 1 &&
      ap beta 0 == 2 && tableChecks n alpha beta betaInv gpl chunks

end CFSG.Sporadic.Th.Native
