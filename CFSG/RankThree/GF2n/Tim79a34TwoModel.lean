module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.GF2n.Tim79a.TwoModel

abbrev Vec4 : Type := Fin 4 → ZMod 2

@[expose] def qf (x : Vec4) : ZMod 2 := x 0 * x 2 + x 1 * x 3

@[expose] def bf (x y : Vec4) : ZMod 2 := x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1

@[expose] def lin4 (c0 c1 c2 c3 : Vec4) (x : Vec4) : Vec4 :=
  x 0 • c0 + x 1 • c1 + x 2 • c2 + x 3 • c3

@[expose] def inFt (x : Vec4) : Prop := x 2 = 0 ∧ x 3 = 0

instance (x : Vec4) : Decidable (inFt x) := by unfold inFt; infer_instance

@[expose] def IsIsom4 (f : Vec4 → Vec4) : Prop :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x, qf (f x) = qf x

@[expose] def Stab4 (f : Vec4 → Vec4) : Prop := ∀ x, inFt x → inFt (f x)

instance (f : Vec4 → Vec4) : Decidable (Stab4 f) := by unfold Stab4; infer_instance

@[expose] def e0 : Vec4 := ![1, 0, 0, 0]
@[expose] def e1 : Vec4 := ![0, 1, 0, 0]
@[expose] def e2 : Vec4 := ![0, 0, 1, 0]
@[expose] def e3 : Vec4 := ![0, 0, 0, 1]

theorem qf_add (x y : Vec4) : qf (x + y) = qf x + qf y + bf x y := by
  unfold qf bf
  simp only [Pi.add_apply]
  ring

theorem bf_add_left (x y z : Vec4) : bf (x + y) z = bf x z + bf y z := by
  unfold bf
  simp only [Pi.add_apply]
  ring

theorem vec4_eq_sum (x : Vec4) : x = x 0 • e0 + x 1 • e1 + x 2 • e2 + x 3 • e3 := by
  funext i
  fin_cases i <;> simp [e0, e1, e2, e3]

theorem isIsom4_map_zero {f : Vec4 → Vec4} (hf : IsIsom4 f) : f 0 = 0 := by
  have h := hf.1 0 0
  simp only [add_zero] at h
  exact left_eq_add.mp h

theorem isIsom4_map_smul {f : Vec4 → Vec4} (hf : IsIsom4 f) (c : ZMod 2) (x : Vec4) :
    f (c • x) = c • f x := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by revert c; decide
  · rw [zero_smul, zero_smul, isIsom4_map_zero hf]
  · rw [one_smul, one_smul]

theorem isIsom4_eq_lin {f : Vec4 → Vec4} (hf : IsIsom4 f) :
    f = lin4 (f e0) (f e1) (f e2) (f e3) := by
  funext x
  conv_lhs => rw [vec4_eq_sum x]
  simp only [lin4, hf.1, isIsom4_map_smul hf]

theorem bf_eq (x y : Vec4) : bf x y = qf (x + y) + qf x + qf y := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  unfold qf bf
  simp only [Pi.add_apply]
  linear_combination (-(x 0 * x 2 + x 1 * x 3 + y 0 * y 2 + y 1 * y 3)) * h2

theorem isIsom4_bf {f : Vec4 → Vec4} (hf : IsIsom4 f) (x y : Vec4) :
    bf (f x) (f y) = bf x y := by
  rw [bf_eq, ← hf.1, hf.2, hf.2, hf.2, ← bf_eq]

abbrev Gram4 (c0 c1 c2 c3 : Vec4) : Prop :=
  qf c0 = 0 ∧ qf c1 = 0 ∧ qf c2 = 0 ∧ qf c3 = 0 ∧ bf c0 c1 = 0 ∧ bf c0 c2 = 1 ∧ bf c0 c3 = 0 ∧
  bf c1 c2 = 0 ∧ bf c1 c3 = 1 ∧ bf c2 c3 = 0

theorem isIsom4_gram {f : Vec4 → Vec4} (hf : IsIsom4 f) :
    Gram4 (f e0) (f e1) (f e2) (f e3) := by
  have hq : ∀ x, qf x = 0 → qf (f x) = 0 := fun x hx => by rw [hf.2, hx]
  have hb := isIsom4_bf hf
  refine ⟨hq _ (by decide), hq _ (by decide), hq _ (by decide), hq _ (by decide), ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hb]; decide
  · rw [hb]; decide
  · rw [hb]; decide
  · rw [hb]; decide
  · rw [hb]; decide
  · rw [hb]; decide

@[expose] def bS : Vec4 → Vec4 := lin4 ![1, 0, 0, 0] ![0, 1, 0, 0] ![0, 1, 1, 0] ![1, 0, 0, 1]

@[expose] def tS0 : Vec4 → Vec4 := lin4 ![1, 0, 0, 0] ![1, 1, 0, 0] ![0, 0, 1, 1] ![0, 0, 0, 1]

@[expose] def tS1 : Vec4 → Vec4 := lin4 ![1, 1, 0, 0] ![0, 1, 0, 0] ![0, 0, 1, 0] ![0, 0, 1, 1]

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
theorem siegel_key : ∀ c2 c3 : Vec4, Gram4 e0 e1 c2 c3 →
    (∀ x : Vec4, inFt (lin4 e0 e1 c2 c3 x + x)) → ¬ (∀ x, lin4 e0 e1 c2 c3 x = x) →
    ∀ x, lin4 e0 e1 c2 c3 x = bS x := by decide

theorem siegel_unique {f : Vec4 → Vec4} (hf : IsIsom4 f) (h1 : ∀ x, inFt x → f x = x)
    (h2 : ∀ x, inFt (f x + x)) (h3 : ∃ x, f x ≠ x) : f = bS := by
  have hfe := isIsom4_eq_lin hf
  have c0 : f e0 = e0 := h1 e0 (by decide)
  have c1 : f e1 = e1 := h1 e1 (by decide)
  have hg := isIsom4_gram hf
  rw [c0, c1] at hg hfe
  funext x
  have key := siegel_key (f e2) (f e3) hg
  rw [← hfe] at key
  exact key h2 (fun h => by obtain ⟨y, hy⟩ := h3; exact hy (h y)) x

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
theorem tS0_key : ∀ c1 c2 c3 : Vec4, Gram4 e0 c1 c2 c3 → Stab4 (lin4 e0 c1 c2 c3) →
    (∀ x, lin4 e0 c1 c2 c3 (lin4 e0 c1 c2 c3 x) = x) → ¬ (∀ x, lin4 e0 c1 c2 c3 x = x) →
    (∀ x, qf (lin4 e0 c1 c2 c3 x + x) = 0) → ¬ (∀ x, lin4 e0 c1 c2 c3 x = bS x) →
    ∀ x, lin4 e0 c1 c2 c3 x = tS0 x := by decide

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
theorem tS1_key : ∀ c0 c2 c3 : Vec4, Gram4 c0 e1 c2 c3 → Stab4 (lin4 c0 e1 c2 c3) →
    (∀ x, lin4 c0 e1 c2 c3 (lin4 c0 e1 c2 c3 x) = x) → ¬ (∀ x, lin4 c0 e1 c2 c3 x = x) →
    (∀ x, qf (lin4 c0 e1 c2 c3 x + x) = 0) → ¬ (∀ x, lin4 c0 e1 c2 c3 x = bS x) →
    ∀ x, lin4 c0 e1 c2 c3 x = tS1 x := by decide

theorem tS0_unique {f : Vec4 → Vec4} (hf : IsIsom4 f) (hst : Stab4 f) (hfix : f e0 = e0)
    (hinv : ∀ x, f (f x) = x) (hne : ∃ x, f x ≠ x) (hts : ∀ x, qf (f x + x) = 0)
    (hb : ∃ x, f x ≠ bS x) : f = tS0 := by
  have hfe := isIsom4_eq_lin hf
  have hg := isIsom4_gram hf
  rw [hfix] at hg hfe
  funext x
  have key := tS0_key (f e1) (f e2) (f e3) hg
  rw [← hfe] at key
  exact key hst hinv (fun h => by obtain ⟨y, hy⟩ := hne; exact hy (h y)) hts
    (fun h => by obtain ⟨y, hy⟩ := hb; exact hy (h y)) x

theorem tS1_unique {f : Vec4 → Vec4} (hf : IsIsom4 f) (hst : Stab4 f) (hfix : f e1 = e1)
    (hinv : ∀ x, f (f x) = x) (hne : ∃ x, f x ≠ x) (hts : ∀ x, qf (f x + x) = 0)
    (hb : ∃ x, f x ≠ bS x) : f = tS1 := by
  have hfe := isIsom4_eq_lin hf
  have hg := isIsom4_gram hf
  rw [hfix] at hg hfe
  funext x
  have key := tS1_key (f e0) (f e2) (f e3) hg
  rw [← hfe] at key
  exact key hst hinv (fun h => by obtain ⟨y, hy⟩ := hne; exact hy (h y)) hts
    (fun h => by obtain ⟨y, hy⟩ := hb; exact hy (h y)) x

@[expose] def gens3 : Fin 3 → (Vec4 → Vec4) := ![tS0, tS1, bS]

@[expose] def gens4 (g : Vec4 → Vec4) : Fin 4 → (Vec4 → Vec4) := ![tS0, tS1, bS, g]

@[expose] def evalW {n : ℕ} (gens : Fin n → (Vec4 → Vec4)) : List (Fin n) → (Vec4 → Vec4)
  | [] => id
  | i :: w => gens i ∘ evalW gens w

theorem evalW_mem {n : ℕ} {gens : Fin n → (Vec4 → Vec4)} {Y : Set (Vec4 → Vec4)}
    (hid : id ∈ Y) (hY : ∀ f ∈ Y, ∀ g ∈ Y, f ∘ g ∈ Y) (hg : ∀ i, gens i ∈ Y) :
    ∀ w, evalW gens w ∈ Y
  | [] => hid
  | i :: w => hY _ (hg i) _ (evalW_mem hid hY hg w)

def stabWords : List (List (Fin 3)) := [
  [],
  [0],
  [0, 1, 0],
  [0, 1],
  [1, 0],
  [1],
  [2, 0, 1, 0],
  [2, 0, 1],
  [2],
  [2, 0],
  [2, 1],
  [2, 1, 0]
]

def rhoData : List ((Vec4 → Vec4) × List (Fin 4)) := [
  (lin4 ![0,0,0,1] ![0,0,1,0] ![0,1,0,0] ![1,0,0,0], [3, 2]),
  (lin4 ![0,0,0,1] ![0,0,1,0] ![0,1,1,0] ![1,0,0,1], [3]),
  (lin4 ![0,0,0,1] ![0,0,1,1] ![1,1,0,0] ![1,0,0,0], [3, 2, 0]),
  (lin4 ![0,0,0,1] ![0,0,1,1] ![1,1,1,1] ![1,0,0,1], [3, 0]),
  (lin4 ![0,0,0,1] ![1,0,0,0] ![0,1,0,0] ![0,0,1,0], [3, 3, 2, 0, 1, 0]),
  (lin4 ![0,0,0,1] ![1,0,0,0] ![1,1,0,0] ![0,0,1,1], [3, 3, 0, 1]),
  (lin4 ![0,0,0,1] ![1,0,0,1] ![0,1,1,0] ![0,0,1,0], [3, 3, 1, 0]),
  (lin4 ![0,0,0,1] ![1,0,0,1] ![1,1,1,1] ![0,0,1,1], [3, 3, 2, 1]),
  (lin4 ![0,0,1,0] ![0,0,0,1] ![1,0,0,0] ![0,1,0,0], [3, 2, 0, 1, 0]),
  (lin4 ![0,0,1,0] ![0,0,0,1] ![1,0,0,1] ![0,1,1,0], [3, 0, 1, 0]),
  (lin4 ![0,0,1,0] ![0,0,1,1] ![1,1,0,0] ![0,1,0,0], [3, 2, 1, 0]),
  (lin4 ![0,0,1,0] ![0,0,1,1] ![1,1,1,1] ![0,1,1,0], [3, 1, 0]),
  (lin4 ![0,0,1,0] ![0,1,0,0] ![1,0,0,0] ![0,0,0,1], [3, 0, 1, 0, 3, 2]),
  (lin4 ![0,0,1,0] ![0,1,0,0] ![1,1,0,0] ![0,0,1,1], [3, 0, 1, 0, 3, 1]),
  (lin4 ![0,0,1,0] ![0,1,1,0] ![1,0,0,1] ![0,0,0,1], [3, 0, 1, 0, 3, 0]),
  (lin4 ![0,0,1,0] ![0,1,1,0] ![1,1,1,1] ![0,0,1,1], [3, 0, 1, 0, 3, 2, 0, 1]),
  (lin4 ![0,0,1,1] ![0,0,0,1] ![1,0,0,0] ![1,1,0,0], [3, 2, 0, 1]),
  (lin4 ![0,0,1,1] ![0,0,0,1] ![1,0,0,1] ![1,1,1,1], [3, 0, 1]),
  (lin4 ![0,0,1,1] ![0,0,1,0] ![0,1,0,0] ![1,1,0,0], [3, 2, 1]),
  (lin4 ![0,0,1,1] ![0,0,1,0] ![0,1,1,0] ![1,1,1,1], [3, 1]),
  (lin4 ![0,0,1,1] ![1,1,0,0] ![0,1,0,0] ![0,0,1,0], [3, 0, 1, 3, 1, 0]),
  (lin4 ![0,0,1,1] ![1,1,0,0] ![1,0,0,0] ![0,0,0,1], [3, 0, 1, 3, 2, 0]),
  (lin4 ![0,0,1,1] ![1,1,1,1] ![0,1,1,0] ![0,0,1,0], [3, 0, 1, 3, 2, 0, 1, 0]),
  (lin4 ![0,0,1,1] ![1,1,1,1] ![1,0,0,1] ![0,0,0,1], [3, 0, 1, 3]),
  (lin4 ![0,1,0,0] ![0,0,1,0] ![0,0,0,1] ![1,0,0,0], [3, 3, 2, 0, 1, 0]),
  (lin4 ![0,1,0,0] ![0,0,1,0] ![0,0,1,1] ![1,1,0,0], [3, 3, 1, 0]),
  (lin4 ![0,1,0,0] ![0,1,1,0] ![1,0,0,1] ![1,0,0,0], [3, 0, 3, 2, 1, 0]),
  (lin4 ![0,1,0,0] ![0,1,1,0] ![1,1,1,1] ![1,1,0,0], [3, 0, 3, 0, 1, 0]),
  (lin4 ![0,1,1,0] ![0,0,1,0] ![0,0,0,1] ![1,0,0,1], [3, 3, 0, 1]),
  (lin4 ![0,1,1,0] ![0,0,1,0] ![0,0,1,1] ![1,1,1,1], [3, 3, 2, 0]),
  (lin4 ![0,1,1,0] ![0,1,0,0] ![1,0,0,0] ![1,0,0,1], [3, 0, 3, 1]),
  (lin4 ![0,1,1,0] ![0,1,0,0] ![1,1,0,0] ![1,1,1,1], [3, 0, 3, 2]),
  (lin4 ![0,1,1,0] ![1,0,0,1] ![0,0,0,1] ![0,0,1,0], [2, 0, 1, 0, 3]),
  (lin4 ![0,1,1,0] ![1,0,0,1] ![1,0,0,0] ![0,1,0,0], [2, 0, 1, 0, 3, 2]),
  (lin4 ![0,1,1,0] ![1,1,1,1] ![0,0,1,1] ![0,0,1,0], [2, 0, 1, 0, 3, 0]),
  (lin4 ![0,1,1,0] ![1,1,1,1] ![1,1,0,0] ![0,1,0,0], [2, 0, 1, 0, 3, 2, 0]),
  (lin4 ![1,0,0,0] ![0,0,0,1] ![0,0,1,0] ![0,1,0,0], [3, 0, 1, 0, 3, 2]),
  (lin4 ![1,0,0,0] ![0,0,0,1] ![0,0,1,1] ![1,1,0,0], [3, 0, 1, 0, 3, 0]),
  (lin4 ![1,0,0,0] ![1,0,0,1] ![0,1,1,0] ![0,1,0,0], [3, 1, 0, 3, 2, 0]),
  (lin4 ![1,0,0,0] ![1,0,0,1] ![1,1,1,1] ![1,1,0,0], [3, 1, 0, 3]),
  (lin4 ![1,0,0,1] ![0,0,0,1] ![0,0,1,0] ![0,1,1,0], [3, 0, 1, 0, 3, 1]),
  (lin4 ![1,0,0,1] ![0,0,0,1] ![0,0,1,1] ![1,1,1,1], [3, 0, 1, 0, 3, 2, 1, 0]),
  (lin4 ![1,0,0,1] ![0,1,1,0] ![0,0,1,0] ![0,0,0,1], [2, 0, 1, 0, 3, 0, 1, 0]),
  (lin4 ![1,0,0,1] ![0,1,1,0] ![0,1,0,0] ![1,0,0,0], [2, 0, 1, 0, 3, 2, 0, 1, 0]),
  (lin4 ![1,0,0,1] ![1,0,0,0] ![0,1,0,0] ![0,1,1,0], [3, 1, 0, 3, 0, 1]),
  (lin4 ![1,0,0,1] ![1,0,0,0] ![1,1,0,0] ![1,1,1,1], [3, 1, 0, 3, 2, 0, 1, 0]),
  (lin4 ![1,0,0,1] ![1,1,1,1] ![0,0,1,1] ![0,0,0,1], [2, 0, 1, 0, 3, 1, 0]),
  (lin4 ![1,0,0,1] ![1,1,1,1] ![1,1,0,0] ![1,0,0,0], [2, 0, 1, 0, 3, 2, 1, 0]),
  (lin4 ![1,1,0,0] ![0,0,1,1] ![0,0,0,1] ![1,0,0,0], [3, 0, 3, 2, 0, 1]),
  (lin4 ![1,1,0,0] ![0,0,1,1] ![0,0,1,0] ![0,1,0,0], [3, 0, 3, 1]),
  (lin4 ![1,1,0,0] ![1,1,1,1] ![0,1,1,0] ![0,1,0,0], [3, 3, 0, 1]),
  (lin4 ![1,1,0,0] ![1,1,1,1] ![1,0,0,1] ![1,0,0,0], [3, 3, 2, 1]),
  (lin4 ![1,1,1,1] ![0,0,1,1] ![0,0,0,1] ![1,0,0,1], [3, 0, 3, 0, 1, 0]),
  (lin4 ![1,1,1,1] ![0,0,1,1] ![0,0,1,0] ![0,1,1,0], [3, 0, 3, 2]),
  (lin4 ![1,1,1,1] ![0,1,1,0] ![0,0,1,0] ![0,0,1,1], [2, 0, 1, 0, 3, 0, 1]),
  (lin4 ![1,1,1,1] ![0,1,1,0] ![0,1,0,0] ![1,1,0,0], [2, 0, 1, 0, 3, 2, 0, 1]),
  (lin4 ![1,1,1,1] ![1,0,0,1] ![0,0,0,1] ![0,0,1,1], [2, 0, 1, 0, 3, 1]),
  (lin4 ![1,1,1,1] ![1,0,0,1] ![1,0,0,0] ![1,1,0,0], [2, 0, 1, 0, 3, 2, 1]),
  (lin4 ![1,1,1,1] ![1,1,0,0] ![0,1,0,0] ![0,1,1,0], [3, 3, 2, 0]),
  (lin4 ![1,1,1,1] ![1,1,0,0] ![1,0,0,0] ![1,0,0,1], [3, 3, 1, 0])
]

def rho0 : Vec4 → Vec4 := lin4 ![0,0,0,1] ![0,0,1,0] ![0,1,1,0] ![1,0,0,1]

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
theorem stab_gen_aux : ∀ c0 c1 c2 c3 : Vec4, Gram4 c0 c1 c2 c3 → Stab4 (lin4 c0 c1 c2 c3) →
    ∃ w ∈ stabWords, ∀ x, lin4 c0 c1 c2 c3 x = evalW gens3 w x := by decide +kernel

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
theorem rhoData_complete : ∀ c0 c1 c2 c3 : Vec4, Gram4 c0 c1 c2 c3 → ¬ Stab4 (lin4 c0 c1 c2 c3) →
    ∃ p ∈ rhoData, ∀ x, lin4 c0 c1 c2 c3 x = p.1 x := by decide +kernel

set_option maxRecDepth 100000 in
theorem rhoData_sound : ∀ p ∈ rhoData, ∀ x, evalW (gens4 p.1) p.2 x = rho0 x := by
  decide +kernel

theorem stab_mem {Y : Set (Vec4 → Vec4)} (hid : id ∈ Y) (hY : ∀ f ∈ Y, ∀ g ∈ Y, f ∘ g ∈ Y)
    (h0 : tS0 ∈ Y) (h1 : tS1 ∈ Y) (hb : bS ∈ Y) {f : Vec4 → Vec4} (hf : IsIsom4 f)
    (hst : Stab4 f) : f ∈ Y := by
  obtain ⟨w, -, hw⟩ := stab_gen_aux (f e0) (f e1) (f e2) (f e3) (isIsom4_gram hf)
    (by rw [← isIsom4_eq_lin hf]; exact hst)
  have hfe : f = evalW gens3 w := by
    funext x
    rw [← hw x, ← isIsom4_eq_lin hf]
  rw [hfe]
  refine evalW_mem hid hY (fun i => ?_) w
  fin_cases i <;> assumption

theorem rho0_cube : ∀ x, rho0 (rho0 (rho0 x)) = x := by decide

theorem rho0_prop :
    bf e0 ((rho0 ∘ rho0) e0) = 0 ∧ (rho0 ∘ rho0) e0 ≠ e0 ∧ (rho0 ∘ rho0) e0 ≠ 0 ∧ (∀ x, (rho0 ∘ rho0) (tS0 x) = tS0 ((rho0 ∘ rho0) x)) ∧
      bS ((rho0 ∘ rho0) e0) ≠ (rho0 ∘ rho0) e0 ∧ bS (rho0 (bS ((rho0 ∘ rho0) e0))) ≠ rho0 (bS ((rho0 ∘ rho0) e0)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem rho0_mem {Y : Set (Vec4 → Vec4)} (hid : id ∈ Y) (hY : ∀ f ∈ Y, ∀ g ∈ Y, f ∘ g ∈ Y)
    (h0 : tS0 ∈ Y) (h1 : tS1 ∈ Y) (hb : bS ∈ Y)
    (hg : ∃ g ∈ Y, IsIsom4 g ∧ ¬ Stab4 g) : rho0 ∈ Y := by
  obtain ⟨g, hgY, hgi, hgs⟩ := hg
  obtain ⟨p, hp, hpg⟩ := rhoData_complete (g e0) (g e1) (g e2) (g e3) (isIsom4_gram hgi)
    (by rw [← isIsom4_eq_lin hgi]; exact hgs)
  have hge : g = p.1 := by
    funext x
    rw [← hpg x, ← isIsom4_eq_lin hgi]
  have hev : evalW (gens4 g) p.2 = rho0 := by
    funext x
    rw [hge]
    exact rhoData_sound p hp x
  rw [← hev]
  refine evalW_mem hid hY (fun i => ?_) p.2
  fin_cases i
  · exact h0
  · exact h1
  · exact hb
  · exact hgY

set_option synthInstance.maxSize 1000 in
theorem perp_span : ∀ x y : Vec4, x ≠ 0 → y ≠ 0 → x ≠ y → bf x y = 0 →
    ∀ z, bf z x = 0 → bf z y = 0 → z = 0 ∨ z = x ∨ z = y ∨ z = x + y := by decide

end CFSG.RankThree.GF2n.Tim79a.TwoModel
