module

public import Certificates.Data.GMS78RuCheck

public section

namespace CFSG.GMS78RuSim

open CFSG.GMS78Ru

abbrev Lin8 : Type := Fin 8 × Fin 8 × Fin 8

@[expose] def linApply (r : Lin8) (t : Fin 8) : Fin 8 :=
  (if t.val.testBit 0 then r.1 else 0) ^^^ (if t.val.testBit 1 then r.2.1 else 0) ^^^
    (if t.val.testBit 2 then r.2.2 else 0)

@[expose] def linComp (r s : Lin8) : Lin8 := (linApply r s.1, linApply r s.2.1, linApply r s.2.2)

@[expose] def linId : Lin8 := (1, 2, 4)

@[expose] def glList : List Lin8 :=
  (all8.flatMap fun a => all8.flatMap fun b => all8.map fun c => (a, b, c)).filter
    fun r => indep3 r.1 r.2.1 r.2.2

@[expose] def linInv (r : Lin8) : Lin8 := (glList.find? fun s => linComp r s == linId).getD linId

@[expose] def invList : List Lin8 := glList.filter fun r => r != linId && linComp r r == linId

abbrev M3 : Type := Fin 3 → Fin 3 → Bool

@[expose] def bmul (A B : M3) : M3 := fun i j =>
  (A i 0 && B 0 j) ^^ (A i 1 && B 1 j) ^^ (A i 2 && B 2 j)

@[expose] def rhoMat (r : Lin8) : M3 := fun i j =>
  (match j with | 0 => r.1 | 1 => r.2.1 | 2 => r.2.2).val.testBit i.val

@[expose] def slToMat (m : Nat) : M3 := fun i j =>
  match i, j with
  | 0, 1 => m.testBit 0 | 0, 2 => m.testBit 1 | 1, 0 => m.testBit 2
  | 1, 2 => m.testBit 3 | 2, 0 => m.testBit 4 | 2, 1 => m.testBit 5
  | 0, 0 => m.testBit 6 | 2, 2 => m.testBit 7
  | 1, 1 => m.testBit 6 ^^ m.testBit 7

@[expose] def bitVal (b : Bool) (k : Nat) : Nat := if b then 2 ^ k else 0

@[expose] def matToSl (A : M3) : Nat :=
  bitVal (A 0 1) 0 + bitVal (A 0 2) 1 + bitVal (A 1 0) 2 + bitVal (A 1 2) 3 + bitVal (A 2 0) 4 +
    bitVal (A 2 1) 5 + bitVal (A 0 0) 6 + bitVal (A 2 2) 7

@[expose] def adMat (r : Lin8) : List Nat :=
  (List.range 8).map fun k => matToSl (bmul (bmul (rhoMat r) (slToMat (2 ^ k))) (rhoMat (linInv r)))

@[expose] def sel (m k c : Nat) : Nat := if m.testBit k then c else 0

@[expose] def maskApply (cols : List Nat) (m : Nat) : Nat :=
  sel m 0 (cols.getD 0 0) ^^^ sel m 1 (cols.getD 1 0) ^^^ sel m 2 (cols.getD 2 0) ^^^
    sel m 3 (cols.getD 3 0) ^^^ sel m 4 (cols.getD 4 0) ^^^ sel m 5 (cols.getD 5 0) ^^^
    sel m 6 (cols.getD 6 0) ^^^ sel m 7 (cols.getD 7 0)

@[expose] def sCoeff (p q s : Fin 8) : Bool × Bool :=
  (s == p || s == (p ^^^ q), s == q || s == (p ^^^ q))

@[expose] def selB (b : Bool) (c : Nat) : Nat := if b then c else 0

@[expose] def xApply (X : List Nat) (p q : Fin 8) (w : V3) : Nat :=
  selB (w.1.val.testBit 0) (X.getD 0 0) ^^^ selB (w.2.1.val.testBit 0) (X.getD 1 0) ^^^
    selB (sCoeff p q w.2.2).1 (X.getD 2 0) ^^^ selB (w.1.val.testBit 1) (X.getD 3 0) ^^^
    selB (w.2.1.val.testBit 1) (X.getD 4 0) ^^^ selB (sCoeff p q w.2.2).2 (X.getD 5 0) ^^^
    selB (w.1.val.testBit 2) (X.getD 6 0) ^^^ selB (w.2.1.val.testBit 2) (X.getD 7 0)

@[expose] def selV (b : Bool) (v : V3) : V3 := if b then v else (0, 0, 0)

@[expose] def xiApply (Xi : List V3) (m : Nat) : V3 :=
  addV (selV (m.testBit 0) (Xi.getD 0 (0, 0, 0))) <| addV (selV (m.testBit 1) (Xi.getD 1 (0, 0, 0)))
    <| addV (selV (m.testBit 2) (Xi.getD 2 (0, 0, 0))) <| addV (selV (m.testBit 3)
    (Xi.getD 3 (0, 0, 0))) <| addV (selV (m.testBit 4) (Xi.getD 4 (0, 0, 0))) <| addV
    (selV (m.testBit 5) (Xi.getD 5 (0, 0, 0))) <| addV (selV (m.testBit 6) (Xi.getD 6 (0, 0, 0)))
    (selV (m.testBit 7) (Xi.getD 7 (0, 0, 0)))

@[expose] def steinData : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3) :=
  [((7, 5, 1, 2), [232, 205, 183, 178, 104, 46, 61, 158],
      [(4, 3, 3), (2, 4, 2), (6, 3, 2), (7, 6, 3), (2, 7, 3), (3, 1, 1), (4, 5, 2), (1, 2, 0)]),
   ((3, 7, 1, 4), [232, 83, 46, 178, 205, 153, 61, 104],
      [(4, 6, 4), (2, 3, 1), (6, 6, 1), (7, 7, 4), (2, 5, 4), (3, 2, 5), (4, 1, 1), (1, 4, 0)]),
   ((5, 3, 1, 6), [232, 246, 153, 178, 59, 183, 61, 83],
      [(4, 5, 1), (2, 7, 7), (6, 5, 7), (7, 1, 1), (2, 2, 1), (3, 3, 6), (4, 4, 7), (1, 6, 0)]),
   ((1, 1, 2, 4), [232, 104, 183, 178, 158, 46, 61, 165],
      [(4, 4, 6), (2, 2, 4), (6, 4, 4), (7, 3, 6), (2, 6, 6), (3, 5, 2), (4, 7, 4), (1, 1, 0)]),
   ((2, 6, 2, 5), [232, 59, 153, 178, 83, 46, 61, 205],
      [(4, 7, 2), (2, 6, 5), (6, 7, 5), (7, 5, 2), (2, 1, 2), (3, 4, 7), (4, 2, 5), (1, 3, 0)]),
   ((4, 2, 3, 4), [232, 158, 46, 178, 165, 183, 61, 246],
      [(4, 2, 7), (2, 1, 3), (6, 2, 3), (7, 4, 7), (2, 3, 7), (3, 7, 4), (4, 6, 3), (1, 5, 0)]),
   ((6, 4, 3, 5), [232, 165, 183, 178, 246, 153, 61, 59],
      [(4, 1, 5), (2, 5, 6), (6, 1, 6), (7, 2, 5), (2, 4, 5), (3, 6, 3), (4, 3, 6), (1, 7, 0)])]

@[expose] def all256 : List Nat := List.range 256

@[expose] def m3Eq (A B : M3) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j => A i j == B i j

@[expose] def m3One : M3 := fun i j => decide (i = j)

@[expose] def s0Check : Bool :=
  steinData.map Prod.fst == specialList &&
  (glList.all fun r => linComp r (linInv r) == linId && linComp (linInv r) r == linId &&
    m3Eq (bmul (rhoMat r) (rhoMat (linInv r))) m3One &&
    m3Eq (bmul (rhoMat (linInv r)) (rhoMat r)) m3One) &&
  (all256.all fun m => matToSl (slToMat m) == m) &&
  (glList.all fun r => let A := adMat r
    all256.all fun m => m3Eq (slToMat (maskApply A m))
      (bmul (bmul (rhoMat r) (slToMat m)) (rhoMat (linInv r)))) &&
  steinData.all fun d =>
    ((wList d.1.2.2.1 d.1.2.2.2).all fun w =>
      xiApply d.2.2 (xApply d.2.1 d.1.2.2.1 d.1.2.2.2 w) == w) &&
    all256.all fun m => xApply d.2.1 d.1.2.2.1 d.1.2.2.2 (xiApply d.2.2 m) == m &&
      (lamList d.1.2.2.1 d.1.2.2.2).contains (xiApply d.2.2 m).2.2

@[expose] def s1Check : Bool :=
  steinData.all fun d =>
    glList.all fun r =>
      let A := adMat r
      (wList d.1.2.2.1 d.1.2.2.2).all fun w =>
        sqN d.1.1 d.1.2.1 (xiApply d.2.2 (maskApply A (xApply d.2.1 d.1.2.2.1 d.1.2.2.2 w))) ==
          linApply r (sqN d.1.1 d.1.2.1 w)

@[expose] def s2aCheck : Bool :=
  invList.all fun r₁ => invList.all fun r₂ =>
    r₁ == r₂ || linComp r₁ r₂ != linComp r₂ r₁ ||
      (let A₁ := adMat r₁
       let A₂ := adMat r₂
       decide ((all256.filter fun m => maskApply A₁ m == m && maskApply A₂ m == m).length ≤ 4))

@[expose] def s2bCheck : Bool :=
  invList.all fun r₁ => invList.all fun r₂ =>
    r₁ == r₂ || linComp r₁ r₂ != linComp r₂ r₁ ||
      glList.all fun r => linComp r r₁ != linComp r₁ r || linComp r r₂ != linComp r₂ r ||
        [linId, r₁, r₂, linComp r₁ r₂].contains r

end CFSG.GMS78RuSim
