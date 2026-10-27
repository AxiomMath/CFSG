module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.Quasithin.G11.M12NC

open Equiv Matrix

abbrev V10 : Type := Fin 10 → ZMod 2

abbrev BV : Type := Array Bool

abbrev BM : Type := Array ℕ

@[expose] def getB (A : BM) (i j : Fin 10) : Bool := (A.getD i.val 0).testBit j.val

@[expose] def getV (v : BV) (i : Fin 10) : Bool := v.getD i.val false

@[expose] def mkV (f : Fin 10 → Bool) : BV := Array.ofFn fun i : Fin 10 => f i

@[expose] def xorSum (f : Fin 10 → Bool) : Bool :=
  (List.finRange 10).foldl (fun acc j => xor acc (f j)) false

@[expose] def rowMul (r : ℕ) (B : BM) : ℕ :=
  (List.finRange 10).foldl (fun acc j => if r.testBit j.val then acc ^^^ B.getD j.val 0 else acc) 0

@[expose] def mulB (A B : BM) : BM := Array.ofFn fun i : Fin 10 => rowMul (A.getD i.val 0) B % 1024

@[expose] def mulVB (A : BM) (v : BV) : BV := mkV fun i => xorSum fun j => getB A i j && getV v j

@[expose] def oneB : BM := Array.ofFn fun i : Fin 10 => 2 ^ i.val

@[expose] def zeroB : BV := mkV fun _ => false

@[expose] def boolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolLists n).flatMap fun l => [false :: l, true :: l]

@[expose] def allVecs : List BV := (boolLists 10).map List.toArray

@[expose] def WF (A : BM) : Prop := A.size = 10 ∧ ∀ r ∈ A.toList, r < 1024

instance (A : BM) : Decidable (WF A) := by unfold WF; infer_instance

@[expose] def ga : Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[expose] def gb : Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

@[expose] def crd (u : Fin 12 → ZMod 2) : V10 := fun i => u (Fin.castLE (by omega) i) + u 11

@[expose] def pm (k : Fin 12) : ℕ :=
  if k.val < 10 then 2 ^ k.val else if k.val = 10 then 1023 else 0

@[expose] def rhoB (σ : Perm (Fin 12)) : BM :=
  let r := pm (σ⁻¹ 11)
  Array.ofFn fun i : Fin 10 => pm (σ⁻¹ (Fin.castLE (by omega) i)) ^^^ r

@[expose] def gen2 (x : Fin 2) : Perm (Fin 12) := if x = 0 then ga else gb

@[expose] def evalW (w : List (Fin 2)) : Perm (Fin 12) := (w.map gen2).prod

@[expose] def xs : List (List (Fin 2)) :=
  [[], [0], [1], [1, 0], [0, 1], [1, 1, 0], [1, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0, 1]]

@[expose] def pg0 : List (ℕ × ℕ) :=
    [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3),
     (3, 0), (3, 1), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1),
     (6, 3), (7, 0), (7, 1), (7, 3), (8, 1), (8, 2), (9, 1), (9, 2), (9, 3), (10, 0), (10, 3),
     (11, 0), (12, 0), (12, 2), (12, 3), (14, 0), (15, 1), (16, 2), (17, 0), (18, 1), (18, 2),
     (19, 1), (19, 3), (20, 0), (20, 1), (20, 3), (21, 1), (21, 2), (22, 3), (24, 0), (24, 2),
     (24, 3), (27, 2), (31, 0), (33, 0), (35, 0), (35, 3), (39, 3), (40, 0), (42, 1), (44, 3)]

@[expose] def pg1 : List (ℕ × ℕ) :=
    [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1),
     (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4),
     (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1),
     (7, 3), (7, 4), (8, 0), (8, 1), (8, 3), (8, 4), (9, 2), (9, 4), (10, 1), (10, 2), (10, 3),
     (10, 4), (11, 1), (11, 2), (11, 3), (11, 4), (12, 0), (12, 3), (12, 4), (13, 0), (13, 4),
     (14, 2), (14, 3), (15, 0), (15, 2), (15, 3), (15, 4), (16, 4), (17, 0), (17, 4), (18, 0),
     (18, 1), (18, 2), (18, 3), (18, 4), (19, 1), (19, 4), (20, 2), (20, 4), (21, 0), (21, 4),
     (22, 0), (22, 1), (22, 2), (22, 3), (22, 4), (23, 0), (23, 1), (23, 3), (23, 4), (24, 2),
     (24, 3), (24, 4), (25, 0), (25, 1), (25, 3), (27, 1), (28, 2), (28, 4), (29, 1), (29, 3),
     (30, 0), (30, 1), (30, 3), (30, 4), (31, 2), (32, 1), (32, 2), (33, 4), (34, 4), (35, 2),
     (36, 0), (36, 2), (36, 3), (36, 4), (37, 4), (39, 0), (39, 4), (40, 4), (41, 3), (42, 3),
     (43, 0), (43, 1), (47, 4), (51, 0), (54, 1), (54, 2), (54, 4), (55, 1), (55, 3), (57, 0),
     (61, 3), (65, 4), (69, 3)]

@[expose] def zidx : ℕ := 11

structure Objs where
  tau : BM
  ra : BM
  rb : BM
  rbb : BM
  gens0 : List BM
  gens1 : List BM
  L0 : Array BM
  L1 : Array BM
  spanM : BM
  Minv : BM
  w0 : BV
  uz : BV
  wit : List (ℕ × BV)

@[expose] def TauOK (O : Objs) : Prop :=
  mulB O.tau O.tau = oneB ∧ mulB O.tau O.ra = mulB O.ra O.tau ∧ mulB O.tau O.rb = mulB O.rbb O.tau

@[expose] def TreeOK (L : Array BM) (gs : List BM) (pg : List (ℕ × ℕ)) (n k : ℕ) : Prop :=
  L.size = n + 1 ∧ pg.length = n ∧ gs.length = k ∧ L[0]! = oneB ∧
    ∀ i < n, (pg[i]!).1 ≤ i ∧ (pg[i]!).2 < k ∧ L[i + 1]! = mulB L[(pg[i]!).1]! gs[(pg[i]!).2]!

@[expose] def ClosedOK (L : Array BM) (gs : List BM) : Prop :=
  L.toList.Nodup ∧ ∀ x ∈ L.toList, ∀ g ∈ gs, mulB x g ∈ L.toList

@[expose] def Fix0 (O : Objs) (u : BV) : Prop :=
  (∀ g ∈ O.gens0, mulVB g u = u) → u = zeroB ∨ u = O.w0

instance (O : Objs) (u : BV) : Decidable (Fix0 O u) := by unfold Fix0; infer_instance

@[expose] def FixOK (O : Objs) : Prop :=
  (∀ u ∈ allVecs, Fix0 O u) ∧ O.w0 ≠ zeroB ∧ ∀ g ∈ O.gens1, mulVB g O.w0 = O.w0

@[expose] def SpanOK (O : Objs) : Prop :=
  mulB O.spanM O.Minv = oneB ∧
    ∀ i j : Fin 10, getB O.spanM i j = getV (mulVB (rhoB (evalW (xs.getD j.val []))) O.w0) i

@[expose] def ZOK (O : Objs) : Prop :=
  mulVB O.L1[zidx]! O.uz = O.uz ∧ O.uz ≠ zeroB ∧ O.uz ≠ O.w0

@[expose] def WitFor (O : Objs) (x : BM) (p : ℕ × BV) : Prop :=
  O.L1[p.1]! = x ∧ p.2 ≠ zeroB ∧ p.2 ≠ O.w0 ∧
    ∀ y ∈ O.L1.toList, mulB y x = mulB x y → mulVB y p.2 = p.2

instance (O : Objs) (x : BM) (p : ℕ × BV) : Decidable (WitFor O x p) := by
  unfold WitFor; infer_instance

@[expose] def WitOK (O : Objs) : Prop :=
  ∀ x ∈ O.L1.toList, mulB x x = oneB → x ≠ oneB → x ≠ O.L1[zidx]! → ∃ p ∈ O.wit, WitFor O x p

@[expose] def FixBoundOK (O : Objs) : Prop :=
  ∀ x ∈ O.L1.toList, mulB x x = oneB → x ≠ oneB →
    (allVecs.filter fun u => decide (mulVB x u = u)).length ≤ 128

@[expose] def WFOK (O : Objs) : Prop :=
  (∀ x ∈ O.L0.toList, WF x) ∧ (∀ x ∈ O.L1.toList, WF x)

@[expose] def Stmt (O : Objs) : Prop :=
  TauOK O ∧ TreeOK O.L0 O.gens0 pg0 63 4 ∧ TreeOK O.L1 O.gens1 pg1 127 5 ∧
    ClosedOK O.L0 O.gens0 ∧ ClosedOK O.L1 O.gens1 ∧ FixOK O ∧ SpanOK O ∧ ZOK O ∧ WitOK O ∧
    FixBoundOK O ∧ WFOK O

instance (O : Objs) : Decidable (TauOK O) := by unfold TauOK; infer_instance

instance (L : Array BM) (gs : List BM) (pg : List (ℕ × ℕ)) (n k : ℕ) :
    Decidable (TreeOK L gs pg n k) := by
  unfold TreeOK; infer_instance

instance (L : Array BM) (gs : List BM) : Decidable (ClosedOK L gs) := by
  unfold ClosedOK; infer_instance

instance (O : Objs) : Decidable (FixOK O) := by unfold FixOK; infer_instance

instance (O : Objs) : Decidable (SpanOK O) := by unfold SpanOK; infer_instance

instance (O : Objs) : Decidable (ZOK O) := by unfold ZOK; infer_instance

instance (O : Objs) : Decidable (WitOK O) := by unfold WitOK; infer_instance

instance (O : Objs) : Decidable (FixBoundOK O) := by unfold FixBoundOK; infer_instance

instance (O : Objs) : Decidable (WFOK O) := by unfold WFOK; infer_instance

instance (O : Objs) : Decidable (Stmt O) := by unfold Stmt; infer_instance

end CFSG.Quasithin.G11.M12NC
