module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSMatrices
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

public section

namespace Certificates.ExcModel

open CFSG.StandardType.ZS

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) (ZMod 13)

structure M13 (n : ℕ) where
  val : Mat n

@[expose, noinline] def tabMat {n : ℕ} (T : List (List (ZMod 13))) : Mat n :=
  Matrix.of fun i j => (T.getD i []).getD j 0

@[expose] def strict {n : ℕ} (A : Mat n) : M13 n :=
  ⟨tabMat (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => A i j)⟩

@[expose] def r13 (x : ℕ) : ZMod 13 := (⟨x % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13)

@[expose] def fmul {n : ℕ} (A B : M13 n) : M13 n :=
  ⟨tabMat (List.ofFn fun i : Fin n => List.ofFn fun k : Fin n =>
    r13 (Fin.foldl n (fun (acc : ℕ) j => acc + (A.val i j).val * (B.val j k).val) 0))⟩

@[expose] def feq {n : ℕ} (A B : M13 n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j => decide ((A.val i j).val = (B.val i j).val)

@[expose] def isOne {n : ℕ} (A : M13 n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide ((A.val i j).val = if i = j then 1 else 0)

@[expose] def fmem {n : ℕ} (y : M13 n) (L : List (M13 n)) : Bool := L.any fun x => feq y x

@[expose] def involCheck {n : ℕ} (S : List (M13 n)) : Bool := S.all fun s => isOne (fmul s s)

@[expose] def conjRound {n : ℕ} (S : List (M13 n)) (st : List (M13 n) × List (M13 n)) :
    List (M13 n) × List (M13 n) :=
  st.1.foldl (fun q x => S.foldl (fun q s =>
    let y := fmul (fmul s x) s
    if fmem y q.2 then q else (q.1 ++ [y], q.2 ++ [y])) q) ([], st.2)

@[expose] def classList {n : ℕ} (S : List (M13 n)) : List (M13 n) :=
  ((conjRound S)^[12] ([S.headD (strict 1)], [S.headD (strict 1)])).2

@[expose] def closedCheck {n : ℕ} (S L : List (M13 n)) : Bool :=
  L.all fun x => S.all fun s => fmem (fmul (fmul s x) s) L

@[expose] def coverCheck {n : ℕ} (R L : List (M13 n)) : Bool := R.all fun g => fmem g L

@[expose] def growRound {n : ℕ} (gs : List (M13 n)) (st : List (M13 n) × List (M13 n)) :
    List (M13 n) × List (M13 n) :=
  st.1.foldl (fun q e => gs.foldl (fun q g =>
    if 48 < q.2.length then q else
      let y := fmul e g
      if fmem y q.2 then q else (q.1 ++ [y], q.2 ++ [y])) q) ([], st.2)

@[expose] def growList {n : ℕ} (gs : List (M13 n)) : List (M13 n) :=
  ((growRound gs)^[8] ([strict 1], [strict 1])).2

@[expose] def bigCheck {n : ℕ} (gs : List (M13 n)) : Bool := decide (48 < (growList gs).length)

@[expose] def a2 {n : ℕ} (a b : M13 n) : Bool :=
  let p := fmul a b
  !(isOne p) && isOne (fmul (fmul p p) p)

@[expose] def partnerCheck {n : ℕ} (r0 : M13 n) (L : List (M13 n)) : Bool :=
  L.all fun x => !(a2 r0 x) ||
    L.any fun t => !(feq (fmul t r0) (fmul r0 t) && feq (fmul t x) (fmul x t)) && bigCheck [r0, x, t]

@[expose] def rowCheck {n : ℕ} (S R : List (M13 n)) : Bool :=
  let L := classList S
  involCheck S && closedCheck S L && coverCheck R L && partnerCheck (S.headD (strict 1)) L

@[expose] def ctList (_ : Unit := ()) : List ((Fin 6 → ZMod 13) × (Fin 6 → ZMod 13)) :=
  ((List.finRange 6).flatMap fun i => (List.finRange 6).flatMap fun j =>
    if i < j then (List.range 3).map fun k =>
      (Pi.single i 1 - Pi.single j (om ^ k), Pi.single i 1 - Pi.single j (om ^ (2 * k)))
    else []) ++
  ([0, 1, 2].flatMap fun t1 => [0, 1, 2].flatMap fun t2 => [0, 1, 2].flatMap fun t3 =>
    [0, 1, 2].flatMap fun t4 => [0, 1, 2].flatMap fun t5 =>
      if (t1 + t2 + t3 + t4 + t5) % 3 = 0 then
        [((fun m : Fin 6 => om ^ (![0, t1, t2, t3, t4, t5] m)),
          (fun m : Fin 6 => om ^ (2 * ![0, t1, t2, t3, t4, t5] m)))]
      else [])

@[expose] def k6R (_ : Unit := ()) : List (M13 6) := (ctList ()).map fun w => strict (herRefl w.1 w.2)

@[expose] def k5R (_ : Unit := ()) : List (M13 6) :=
  ((ctList ()).filter fun w => decide (w.1 0 - w.1 1 = 0)).map fun w => strict (herRefl w.1 w.2)

@[expose] def n4S (_ : Unit := ()) : List (M13 4) :=
  [strict (piMat 0 1 1), strict (piMat 1 2 1), strict (piMat 0 1 5), strict aMat]

@[expose] def en4S (_ : Unit := ()) : List (M13 4) :=
  n4S () ++ [strict (Matrix.diagonal fun i => if i = 3 then -1 else 1)]

@[expose] def k5S (_ : Unit := ()) : List (M13 6) := [20, 9, 25, 41, 3].map fun i => (k5R ()).getD i (strict 1)

@[expose] def k6S (_ : Unit := ()) : List (M13 6) := [41, 121, 19, 50, 83, 6].map fun i => (k6R ()).getD i (strict 1)

end Certificates.ExcModel

end
