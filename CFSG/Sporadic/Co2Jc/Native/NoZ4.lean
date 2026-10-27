module

public import CFSG.Sporadic.Co2Jc.Words
public import CFSG.Sporadic.Co2Jc.Data.Rels
public import CFSG.Sporadic.Co2Jc.Data.NoZ4
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Sporadic.Co2Jc.Native

open CFSG.Sporadic.Co2Jc.Data

structure NoZ4.Tab (R : Type) where
  rows : Array (Array R)
  deriving Inhabited

namespace NoZ4

@[expose] def Tab.ofMat {R : Type} (M : Matrix (Fin 10) (Fin 10) R) : Tab R :=
  ⟨Array.ofFn fun i => Array.ofFn fun j => M i j⟩

@[expose] def Tab.toMat {R : Type} [Inhabited R] (T : Tab R) :
    Matrix (Fin 10) (Fin 10) R :=
  Matrix.of fun i j => (T.rows[i.val]!)[j.val]!

theorem Tab.toMat_ofMat {R : Type} [Inhabited R] (M : Matrix (Fin 10) (Fin 10) R) :
    (Tab.ofMat M).toMat = M := by
  ext i j
  simp [Tab.ofMat, Tab.toMat, Matrix.of, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, i.isLt, j.isLt]
  rfl

@[expose] def Tab.get {R : Type} [Inhabited R] (T : Tab R) (i j : Nat) : R :=
  (T.rows[i % 10]!)[j % 10]!

@[expose] def Tab.mul {R : Type} [Inhabited R] [Semiring R] [Fintype (Fin 10)]
    (A B : Tab R) : Tab R :=
  Tab.ofMat (A.toMat * B.toMat)

@[expose] def Tab.add {R : Type} [Inhabited R] [Add R] [Zero R] (A B : Tab R) : Tab R :=
  Tab.ofMat (A.toMat + B.toMat)

@[expose] def Tab.transpose {R : Type} [Inhabited R] (A : Tab R) : Tab R :=
  Tab.ofMat A.toMat.transpose

@[expose] def Tab.sum {R : Type} [Inhabited R] [Add R] [Zero R] (l : List (Tab R)) : Tab R :=
  l.foldr Tab.add (Tab.ofMat 0)

theorem Tab.toMat_mul {R : Type} [Inhabited R] [Semiring R] [Fintype (Fin 10)]
    (A B : Tab R) : (Tab.mul A B).toMat = A.toMat * B.toMat := by
  rw [Tab.mul, Tab.toMat_ofMat]

theorem Tab.toMat_add {R : Type} [Inhabited R] [Add R] [Zero R] (A B : Tab R) :
    (Tab.add A B).toMat = A.toMat + B.toMat := by
  rw [Tab.add, Tab.toMat_ofMat]

theorem Tab.toMat_sum {R : Type} [Inhabited R] [Add R] [Zero R] (l : List (Tab R)) :
    (Tab.sum l).toMat = (l.map Tab.toMat).sum := by
  induction l with
  | nil => simp [Tab.sum, Tab.toMat_ofMat]
  | cons a l ih =>
    change (Tab.add a (Tab.sum l)).toMat = a.toMat + (l.map Tab.toMat).sum
    rw [Tab.toMat_add, ih]

theorem Tab.toMat_transpose {R : Type} [Inhabited R] (A : Tab R) :
    (Tab.transpose A).toMat = A.toMat.transpose := by
  rw [Tab.transpose, Tab.toMat_ofMat]

abbrev M2 := Matrix (Fin 10) (Fin 10) (ZMod 2)

abbrev M4 := Matrix (Fin 10) (Fin 10) (ZMod 4)

@[expose] def G2 (k : Nat) : M2 :=
  fun j i => if (CFSG.Sporadic.Co2Smith.Native.glNJTab[k]!)[i.val]!.testBit j.val then 1 else 0

@[expose] def G4 (k : Nat) : M4 :=
  (G2 k).map fun x => (x.val : ZMod 4)

@[expose] def G2Tab (k : Nat) : Tab (ZMod 2) := Tab.ofMat (G2 k)

@[expose] def G4Tab (k : Nat) : Tab (ZMod 4) := Tab.ofMat (G4 k)

@[expose] def prod2 (w : List Nat) : Tab (ZMod 2) :=
  w.foldl (fun acc k => Tab.mul acc (G2Tab k)) (Tab.ofMat 1)

@[expose] def prod4 (w : List Nat) : Tab (ZMod 4) :=
  w.foldl (fun acc k => Tab.mul acc (G4Tab k)) (Tab.ofMat 1)

@[expose] def prefList (w : List Nat) : List (Tab (ZMod 2)) :=
  (List.range (w.length + 1)).map fun i => prod2 (w.take i)

@[expose] def suffList (w : List Nat) : List (Tab (ZMod 2)) :=
  (List.range (w.length + 1)).map fun i => prod2 (w.drop i)

private theorem foldl_prod2_toMat (init : Tab (ZMod 2)) (l : List Nat) :
    (l.foldl (fun acc k => Tab.mul acc (G2Tab k)) init).toMat =
      init.toMat * (l.map G2).prod := by
  induction l generalizing init with
  | nil => simp [Tab.toMat_ofMat]
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih (Tab.mul init (G2Tab a)), Tab.mul, Tab.toMat_ofMat]
    simp [G2Tab, Tab.toMat_ofMat, mul_assoc]

theorem prod2_toMat (l : List Nat) : (prod2 l).toMat = (l.map G2).prod := by
  rw [prod2, foldl_prod2_toMat]
  simp [Tab.toMat_ofMat]

private theorem foldl_prod4_toMat (init : Tab (ZMod 4)) (l : List Nat) :
    (l.foldl (fun acc k => Tab.mul acc (G4Tab k)) init).toMat =
      init.toMat * (l.map G4).prod := by
  induction l generalizing init with
  | nil => simp [Tab.toMat_ofMat]
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih (Tab.mul init (G4Tab a)), Tab.mul, Tab.toMat_ofMat]
    simp [G4Tab, Tab.toMat_ofMat, mul_assoc]

theorem prod4_toMat (l : List Nat) : (prod4 l).toMat = (l.map G4).prod := by
  rw [prod4, foldl_prod4_toMat]
  simp [Tab.toMat_ofMat]

theorem prefList_getElem_toMat (w : List Nat) (i : Nat) (hi : i < (prefList w).length) :
    (prefList w)[i].toMat = ((w.take i).map G2).prod := by
  simp [prefList, List.getElem_map, prod2_toMat]

theorem suffList_getElem_toMat (w : List Nat) (i : Nat) (hi : i < (suffList w).length) :
    (suffList w)[i].toMat = ((w.drop i).map G2).prod := by
  simp [suffList, List.getElem_map, prod2_toMat]

@[expose] def Csel (r : Nat) : Tab (ZMod 2) :=
  Tab.ofMat fun a b => if (r, a.val, b.val) ∈ noZ4Sel then 1 else 0

private theorem foldl_add_toMat (l : List Nat) (init : Tab (ZMod 2))
    (f : Nat → Tab (ZMod 2)) :
    (l.foldl (fun acc i => Tab.add acc (f i)) init).toMat =
      init.toMat + (l.map fun i => (f i).toMat).sum := by
  induction l generalizing init with
  | nil => simp [Tab.toMat_ofMat]
  | cons a l ih =>
    rw [List.foldl_cons, ih (Tab.add init (f a)), Tab.toMat_add]
    simp [add_assoc]

@[expose] def coeff2 (k : Nat) : Tab (ZMod 2) :=
  Tab.sum (noZ4Rels.map fun r =>
    let w := rels[r]!
    let pre := prefList w
    let suf := suffList w
    (List.range w.length).foldl (fun acc i =>
      Tab.add acc (if w[i]! = k then
        Tab.mul (Tab.mul (Tab.transpose (pre[i]!)) (Csel r))
          (Tab.transpose (suf[i + 1]!))
      else Tab.ofMat 0)) (Tab.ofMat 0))

private theorem foldl_ite_eq_sum_aux (l : List Nat) (p : Nat → Prop) [DecidablePred p]
    (f : Nat → M2) (init : M2) :
    (l.foldl (fun acc i => if p i then acc + f i else acc) init) =
      init + (l.map (fun i => if p i then f i else 0)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    by_cases h : p a <;> simp [h, ih, add_assoc]

private theorem foldl_ite_eq_sum (l : List Nat) (p : Nat → Prop) [DecidablePred p]
    (f : Nat → M2) :
    (l.foldl (fun acc i => if p i then acc + f i else acc) 0) =
      (l.map (fun i => if p i then f i else 0)).sum := by
  rw [foldl_ite_eq_sum_aux, zero_add]

theorem coeff2_toMat (k : Nat) : (coeff2 k).toMat =
  (noZ4Rels.map fun r =>
    let w := rels[r]!
    (List.range w.length).foldl (fun acc i =>
      if w[i]! = k then
        acc + (prefList w)[i]!.toMat.transpose * (Csel r).toMat *
          (suffList w)[i + 1]!.toMat.transpose
      else acc) 0).sum := by
  rw [coeff2, Tab.toMat_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  rw [foldl_add_toMat]
  simp only [Tab.toMat_ofMat, zero_add]
  rw [foldl_ite_eq_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  by_cases h : (rels[r]!)[i]! = k
  · simp only [h, if_true, Tab.toMat_mul, Tab.toMat_transpose]
  · simp only [h, if_false]
    rw [Tab.toMat_ofMat]

@[expose] def matZero (M : M2) : Bool :=
  (List.finRange 10).all fun j => (List.finRange 10).all fun i => M j i == 0

@[expose] def idEntry (a b : Nat) : Nat := if a % 10 = b % 10 then 1 else 0

@[expose] def Ebit (P : Tab (ZMod 4)) (a b : Nat) : ZMod 4 :=
  if P.get a b = (idEntry a b : ZMod 4) then 0 else 1

@[expose] def EOK : Bool :=
  let P1 := prod4 (rels[1]!)
  let P9 := prod4 (rels[9]!)
  let Pof (r : Nat) : Tab (ZMod 4) := if r = 1 then P1 else P9
  noZ4Sel.all (fun p =>
    p.1 ∈ noZ4Rels && p.2.1 < 10 && p.2.2 < 10 &&
      (Pof p.1).get p.2.1 p.2.2 =
        (idEntry p.2.1 p.2.2 : ZMod 4) + 2 * Ebit (Pof p.1) p.2.1 p.2.2) &&
    (noZ4Rels.map fun r =>
      Finset.univ.sum fun a : Fin 10 =>
        Finset.univ.sum fun b : Fin 10 =>
          (Csel r).toMat a b * (((Ebit (Pof r) a.val b.val).val : ℕ) : ZMod 2)).sum == 1

@[expose] def noZ4RelOK (r : Nat) : Bool :=
  let w := rels[r]!
  r < rels.length && w.all (· < 3) && (List.range 10).all fun i => wordAct w (2 ^ i) == 2 ^ i

@[expose] def noZ4TabOK : Bool :=
  (List.range 3).all fun k => (List.range 10).all fun i =>
    (CFSG.Sporadic.Co2Smith.Native.glNJTab[k]!)[i]! < 1024

end NoZ4

open NoZ4

@[expose] def noZ4OK : Bool :=
  noZ4Rels.all noZ4RelOK && noZ4TabOK &&
    (List.range 3).all (fun k => matZero (coeff2 k).toMat) && EOK

end CFSG.Sporadic.Co2Jc.Native
