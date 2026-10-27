module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

open Matrix

abbrev V := Fin 4 → ZMod 3

abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 3)

def e (i : Fin 4) : V := Pi.single i 1

def fV (v : V) : V := ![v 0, v 1, v 2, v 3]

def fM (A : Mat) : Mat :=
  !![A 0 0, A 0 1, A 0 2, A 0 3; A 1 0, A 1 1, A 1 2, A 1 3; A 2 0, A 2 1, A 2 2, A 2 3;
    A 3 0, A 3 1, A 3 2, A 3 3]

theorem fV_eq (v : V) : fV v = v := by
  ext i; fin_cases i <;> rfl

theorem fM_eq (A : Mat) : fM A = A := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

def mm (A B : Mat) : Mat := fM (A * B)

def mv (A : Mat) (v : V) : V := fV (A *ᵥ v)

def vmm (v : V) (A : Mat) : V := fV (v ᵥ* A)

def mpow (A : Mat) : ℕ → Mat
  | 0 => 1
  | k + 1 => mm (mpow A k) A

theorem mm_eq (A B : Mat) : mm A B = A * B := fM_eq _
theorem mv_eq (A : Mat) (v : V) : mv A v = A *ᵥ v := fV_eq _
theorem vmm_eq (v : V) (A : Mat) : vmm v A = v ᵥ* A := fV_eq _

theorem mpow_eq (A : Mat) (k : ℕ) : mpow A k = A ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [mpow, mm_eq, ih, pow_succ]

def refl (w ψ : V) : Mat := fM (1 + vecMulVec w ψ)

theorem refl_eq (w ψ : V) : refl w ψ = 1 + vecMulVec w ψ := fM_eq _

def dec (n : ℕ) : V := ![(n % 3 : ℕ), (n / 3 % 3 : ℕ), (n / 9 % 3 : ℕ), (n / 27 % 3 : ℕ)]

def enc (v : V) : ℕ := (v 0).val + 3 * (v 1).val + 9 * (v 2).val + 27 * (v 3).val

def allV : List V := (List.range 81).map dec

def nonzeroL : List V := (List.range 80).map fun n => dec (n + 1)

def T0 : Mat := !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def S1 : Mat := !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def Tau : Mat := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
def Cyc : Mat := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]
def Sig01 : Mat := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def Cyc4 : Mat := !![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

def H0L : List Mat :=
  [!![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 2, 0, 0],
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0; 0, 2, 0, 0],
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 2, 0],
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 2, 0, 0; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 2, 0, 0; 0, 0, 2, 0],
    !![1, 0, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0; 0, 2, 0, 0],
    !![1, 0, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0; 0, 2, 0, 0],
    !![1, 0, 0, 0; 0, 0, 0, 2; 0, 1, 0, 0; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 0, 0, 2; 0, 1, 0, 0; 0, 0, 2, 0],
    !![1, 0, 0, 0; 0, 0, 0, 2; 0, 2, 0, 0; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 0, 0, 2; 0, 2, 0, 0; 0, 0, 2, 0],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 2, 0, 0],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 2; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 2; 0, 2, 0, 0],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 2],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 2, 0, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 2, 0, 0; 0, 0, 0, 2],
    !![1, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1; 0, 2, 0, 0],
    !![1, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2; 0, 2, 0, 0],
    !![1, 0, 0, 0; 0, 0, 2, 0; 0, 1, 0, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 0, 2, 0; 0, 1, 0, 0; 0, 0, 0, 2],
    !![1, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2],
    !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0],
    !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0],
    !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 1, 0; 0, 0, 0, 2],
    !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0],
    !![2, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 2, 0, 0],
    !![2, 0, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0; 0, 1, 0, 0],
    !![2, 0, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0; 0, 2, 0, 0],
    !![2, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0],
    !![2, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 2, 0],
    !![2, 0, 0, 0; 0, 0, 0, 1; 0, 2, 0, 0; 0, 0, 1, 0],
    !![2, 0, 0, 0; 0, 0, 0, 1; 0, 2, 0, 0; 0, 0, 2, 0],
    !![2, 0, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0; 0, 1, 0, 0],
    !![2, 0, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0; 0, 2, 0, 0],
    !![2, 0, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0; 0, 1, 0, 0],
    !![2, 0, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0; 0, 2, 0, 0],
    !![2, 0, 0, 0; 0, 0, 0, 2; 0, 1, 0, 0; 0, 0, 1, 0],
    !![2, 0, 0, 0; 0, 0, 0, 2; 0, 1, 0, 0; 0, 0, 2, 0],
    !![2, 0, 0, 0; 0, 0, 0, 2; 0, 2, 0, 0; 0, 0, 1, 0],
    !![2, 0, 0, 0; 0, 0, 0, 2; 0, 2, 0, 0; 0, 0, 2, 0],
    !![2, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![2, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 2, 0, 0],
    !![2, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 2; 0, 1, 0, 0],
    !![2, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 2; 0, 2, 0, 0],
    !![2, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
    !![2, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 0, 1, 0; 0, 2, 0, 0; 0, 0, 0, 1],
    !![2, 0, 0, 0; 0, 0, 1, 0; 0, 2, 0, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1; 0, 2, 0, 0],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2; 0, 1, 0, 0],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2; 0, 2, 0, 0],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 1, 0, 0; 0, 0, 0, 1],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 1, 0, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 1],
    !![2, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0],
    !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0],
    !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0],
    !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1],
    !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0],
    !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0],
    !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0],
    !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 1, 0; 0, 0, 0, 2],
    !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1],
    !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2]]

def SU : List V := [e 1, -e 1, e 2, -e 2, e 3, -e 3]

def ofCols (c : Fin 4 → V) : Mat := Matrix.of fun i j => c j i

def E0L : List V := [e 0, -e 0]

def Fr8 : List V := [e 0, -e 0, e 1, -e 1, e 2, -e 2, e 3, -e 3]

scoped instance (priority := high) decBAllList {α : Type*} (p : α → Prop) [DecidablePred p]
    (L : List α) : Decidable (∀ a ∈ L, p a) := List.decidableBAll p L

scoped instance (priority := high) decBExList {α : Type*} (p : α → Prop) [DecidablePred p]
    (L : List α) : Decidable (∃ a ∈ L, p a) := List.decidableBEx p L

theorem forall_mem_of_all {α : Type*} {L : List α} {p : α → Prop} [DecidablePred p]
    (h : L.all (fun a => decide (p a)) = true) : ∀ a ∈ L, p a :=
  fun a ha => of_decide_eq_true (List.all_eq_true.1 h a ha)

def OkB (w ψ : V) : Prop :=
  (∀ A ∈ H0L, (mv A w = w ∨ mv A w = -w) → mm A (refl w ψ) = mm (refl w ψ) A) ∧
    ((mv (refl w ψ) (e 0) = e 0 ∨ mv (refl w ψ) (e 0) = -e 0) → refl w ψ ∈ H0L)

def rep : Fin 7 → V :=
  ![![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![1, 0, 0, 1], ![1, 0, 1, 1],
    ![1, 1, 1, 1]]

def okL : Fin 7 → List V :=
  ![[![1, 0, 0, 0]], [![0, 0, 0, 1]], [![0, 0, 2, 2]], [], [![1, 0, 0, 0], ![2, 0, 0, 2]],
    [![1, 0, 0, 0], ![2, 0, 1, 1]], [![1, 0, 0, 0], ![1, 1, 1, 1], ![1, 2, 2, 2]]]

def wtU (v : V) : ℕ :=
  (if v 1 ≠ 0 then 1 else 0) + (if v 2 ≠ 0 then 1 else 0) + (if v 3 ≠ 0 then 1 else 0)

def orbOf (v : V) : Fin 7 :=
  if v 0 = 0 then (if wtU v = 1 then 1 else if wtU v = 2 then 2 else 3)
  else (if wtU v = 0 then 0 else if wtU v = 1 then 4 else if wtU v = 2 then 5 else 6)

def hOf (v : V) : Mat :=
  let k := wtU v
  let idx : List (Fin 4) := [1, 2, 3]
  let pairs := List.zip (idx.take (3 - k) ++ idx.drop (3 - k))
    (idx.filter (fun j => decide (v j = 0)) ++ idx.filter (fun j => decide (v j ≠ 0)))
  let col : Fin 4 → V := fun i =>
    if i = 0 then (if v 0 = 0 then 1 else v 0) • e 0 else
      match pairs.lookup i with
      | some j => (if v j = 0 then 1 else v j) • e j
      | none => 0
  fM (ofCols col)

def tab (v : V) : Fin 7 × Mat := (orbOf v, hOf v)

abbrev Cfg := (Fin 7 → Bool) × (Fin 7 → V)

def memOm (c : Cfg) (v : V) : Bool := decide (v ≠ 0) && c.1 (tab v).1

def psiC (c : Cfg) (v : V) : V := mv (tab v).2 (c.2 (tab v).1)

def rC (c : Cfg) (v : V) : Mat := refl v (psiC c v)

def C1 (c : Cfg) : Prop :=
  ∀ w ∈ nonzeroL, memOm c w = true → ∀ w' ∈ nonzeroL, memOm c w' = true →
    memOm c (mv (rC c w) w') = true ∧ psiC c (mv (rC c w) w') = vmm (psiC c w') (rC c w)

def C3 (c : Cfg) : Prop := ∃ v ∈ nonzeroL, memOm c v = true ∧ v 0 = 0

def C4a (c : Cfg) (k : ℕ) : Prop :=
  ∀ w ∈ nonzeroL, memOm c w = true → mpow (mm T0 (rC c w)) k = 1

def C4b (c : Cfg) (k : ℕ) : Prop :=
  ∀ w ∈ nonzeroL, memOm c w = true → ∀ w' ∈ nonzeroL, memOm c w' = true →
    mpow (mm (rC c w) (rC c w')) k = 1

def C4 (c : Cfg) (k : ℕ) : Prop := C4a c k → C4b c k

def W (c : Cfg) : Prop :=
  ∃ a ∈ nonzeroL, memOm c a = true ∧ ∃ b ∈ nonzeroL, memOm c b = true ∧
    mm (mm (rC c a) (rC c b)) Sig01 ∈ H0L

def mA : Fin 7 → Bool := ![true, true, false, false, false, false, false]
def mB : Fin 7 → Bool := ![true, true, false, false, false, false, true]
def mC : Fin 7 → Bool := ![true, true, true, false, true, false, true]
def mD : Fin 7 → Bool := ![true, false, true, false, false, false, true]
def mE : Fin 7 → Bool := ![true, true, true, false, false, true, true]

def pos (v : V) : Bool :=
  if v 0 ≠ 0 then v 0 = 1 else if v 1 ≠ 0 then v 1 = 1 else if v 2 ≠ 0 then v 2 = 1 else v 3 = 1

def lineCount (m : Fin 7 → Bool) : ℕ :=
  ((nonzeroL.filter fun v => m (tab v).1 && pos v).toFinset).card

def Good (c : Cfg) : Prop :=
  c.1 = mA ∨ (c.1 = mB ∧ W c) ∨ (c.1 = mC ∧ W c) ∨ c.1 = mD ∨ c.1 = mE

def optL (k : Fin 7) (m : Bool) : List V := if m then okL k else [0]

def mkCfg (m₁ m₂ m₄ m₅ m₆ : Bool) (p₁ p₂ p₄ p₅ p₆ : V) : Cfg :=
  (![true, m₁, m₂, false, m₄, m₅, m₆], ![![1, 0, 0, 0], p₁, p₂, 0, p₄, p₅, p₆])

end CFSG.RankThree.PartTwo.Sec21.FF81.P51
