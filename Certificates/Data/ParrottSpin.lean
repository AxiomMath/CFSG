module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.NatLog

public section

open scoped BigOperators Matrix

namespace CFSG.RankThree.GF2n.Parrott

abbrev V := Fin 8 → ZMod 2

@[expose] def Ms1 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 1, 0, 1, 1, 0;
     1, 0, 1, 1, 1, 1, 0, 1;
     1, 0, 1, 0, 1, 0, 1, 0;
     0, 0, 1, 1, 1, 0, 0, 1;
     1, 0, 1, 0, 0, 1, 1, 0;
     1, 0, 0, 0, 0, 0, 1, 0;
     0, 1, 0, 1, 0, 0, 0, 1;
     1, 1, 0, 1, 0, 1, 1, 1]

@[expose] def Ms2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 1, 1, 0, 1, 0;
     1, 0, 1, 1, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 1, 0, 1;
     0, 1, 1, 0, 1, 0, 1, 0;
     0, 1, 0, 0, 1, 1, 1, 0;
     0, 1, 0, 1, 0, 0, 1, 0;
     0, 1, 0, 1, 0, 0, 0, 1]

@[expose] def Ms1s2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 1, 1, 0, 0, 0;
     1, 0, 1, 1, 0, 1, 0, 0;
     1, 1, 0, 0, 0, 1, 0, 0;
     0, 1, 1, 0, 0, 0, 0, 0;
     1, 1, 1, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 1, 0, 0, 0;
     1, 1, 0, 1, 0, 1, 0, 1;
     0, 1, 0, 1, 0, 0, 1, 1]

@[expose] def Ms1s2inv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 0, 0, 1, 1, 0, 1;
     1, 0, 0, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 1, 1, 0, 1;
     1, 1, 0, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 1, 0, 1;
     0, 1, 0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 1, 1, 1]

@[expose] def Mt : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     1, 0, 1, 0, 0, 1, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def Mu : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     1, 1, 0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1, 0, 1]

@[expose] def Mv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 1, 1, 0, 1, 0, 0;
     1, 0, 1, 0, 0, 1, 0, 0;
     0, 1, 1, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     1, 0, 0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def QMAT : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     1, 0, 1, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     1, 0, 0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     1, 1, 0, 0, 1, 1, 0, 0]

@[expose] def q (v : V) : ZMod 2 :=
  ∑ i : Fin 8, ∑ j : Fin 8, if j ≤ i then QMAT i j * v i * v j else 0

@[expose] def b (v w : V) : ZMod 2 := q (v + w) + q v + q w

@[expose] def fixCard (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : ℕ :=
  Fintype.card {v : V // M.mulVec v = v}

@[expose] def fixDim (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : ℕ :=
  Nat.log 2 (fixCard M)

@[expose] def Mx : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 1, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 1, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def My : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 1, 0, 0, 1, 1, 1, 1],
      ![1, 0, 0, 1, 0, 1, 1, 1],
      ![0, 1, 1, 0, 1, 0, 0, 0],
      ![1, 1, 1, 0, 1, 1, 1, 1],
      ![0, 0, 1, 0, 1, 0, 1, 0],
      ![0, 1, 0, 0, 0, 1, 1, 1],
      ![1, 0, 0, 0, 0, 1, 1, 0],
      ![1, 1, 1, 1, 1, 1, 0, 1]]

@[expose] def Mf : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 1, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 1, 1, 0, 1, 0, 0],
      ![0, 0, 1, 0, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0],
      ![1, 0, 0, 0, 0, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def MyInv : Matrix (Fin 8) (Fin 8) (ZMod 2) := My * My * My * My

@[expose] def spinLetterMatrix (l : Fin 2 × Bool) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  if l.1 = 0 then Mx else if l.2 then My else MyInv

@[expose] def matWord (w : List (Fin 2 × Bool)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  (w.map spinLetterMatrix).prod

@[expose] def spinStep (l : Fin 2 × Bool) (v : V) : V := spinLetterMatrix l *ᵥ v

@[expose] def evalSpinWordV (w : List (Fin 2 × Bool)) (v : V) : V := w.foldr spinStep v

@[expose] def basis (e : Fin 8) : V := Pi.single e 1

theorem evalSpinWordV_eq_matWord_mulVec (w : List (Fin 2 × Bool)) (v : V) :
    evalSpinWordV w v = matWord w *ᵥ v := by
  induction w with
  | nil => simp [evalSpinWordV, matWord, Matrix.one_mulVec]
  | cons l w ih =>
    change spinLetterMatrix l *ᵥ evalSpinWordV w v = matWord (l :: w) *ᵥ v
    rw [ih]
    change spinLetterMatrix l *ᵥ (matWord w *ᵥ v) = (spinLetterMatrix l * matWord w) *ᵥ v
    rw [Matrix.mulVec_mulVec]

@[expose] def spinRelA2 : List (Fin 2 × Bool) := [(0, true), (0, true)]

@[expose] def spinRelB5 : List (Fin 2 × Bool) :=
  [(1, true), (1, true), (1, true), (1, true), (1, true)]

@[expose] def spinRelAB9 : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true)]

@[expose] def spinRelComm3 : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false),
    (0, true), (1, true), (0, false), (1, false)]

@[expose] def spinRelCommBab2 : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false),
    (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false)]

@[expose] def spinRels : List (List (Fin 2 × Bool)) :=
  [spinRelA2, spinRelB5, spinRelAB9, spinRelComm3, spinRelCommBab2]

@[expose] def bitmask (v : V) : Nat :=
  ∑ i : Fin 8, (v i).val <<< (i : Nat)

theorem testBit_sum_shiftLeft (n : Nat) (b : Fin n → Nat) (hb : ∀ i, b i < 2) (j : Fin n) :
    (∑ i : Fin n, b i <<< (i : Nat)).testBit (j : Nat) = decide (b j = 1) := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have hterm : ∀ i : Fin n,
        b i.succ <<< ((i.succ : Fin (n + 1)) : Nat) = 2 * (b i.succ <<< (i : Nat)) := by
      intro i
      rw [Fin.val_succ, Nat.shiftLeft_succ]
    simp only [Fin.val_zero, Nat.shiftLeft_zero]
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    have hb0 : b 0 < 2 := hb 0
    have h : b 0 + 2 * (∑ i : Fin n, b i.succ <<< (i : Nat)) =
        2 ^ 1 * (∑ i : Fin n, b i.succ <<< (i : Nat)) + b 0 := by
      rw [Nat.add_comm]; rfl
    rcases j with ⟨j, hj⟩
    cases j with
    | zero =>
      rw [h, Nat.testBit_two_pow_mul_add (a := ∑ i : Fin n, b i.succ <<< (i : Nat))
        (b := b 0) (i := 1) hb0 0]
      simp only [Nat.zero_lt_one, ite_true, Nat.zero_sub]
      rw [Nat.testBit_zero, Nat.mod_eq_of_lt hb0]
      congr 1
    | succ j =>
      rw [h, Nat.testBit_two_pow_mul_add (a := ∑ i : Fin n, b i.succ <<< (i : Nat))
        (b := b 0) (i := 1) hb0 (j + 1)]
      simp only [Nat.add_sub_cancel]
      split_ifs with hlt
      · omega
      · exact ih (fun i => b i.succ) (fun i => hb i.succ) ⟨j, by omega⟩

theorem testBit_bitmask (v : V) (j : Fin 8) :
    (bitmask v).testBit (j : Nat) = decide ((v j).val = 1) := by
  rw [bitmask]
  exact testBit_sum_shiftLeft 8 (fun i => (v i).val) (fun i => ZMod.val_lt _) j

theorem bitmask_shiftRight (v : V) (j : Fin 8) :
    (bitmask v >>> (j : Nat)) % 2 = (v j).val := by
  rw [Nat.shiftRight_eq_div_pow, ← Nat.toNat_testBit, testBit_bitmask]
  have h : (v j).val < 2 := ZMod.val_lt _
  by_cases hv : (v j).val = 1
  · simp [hv]
  · have hv0 : (v j).val = 0 := by omega
    simp [hv0]

theorem bitmask_injective : Function.Injective bitmask := by
  intro v w h
  funext j
  exact ZMod.val_injective 2 (by rw [← bitmask_shiftRight v j, h, bitmask_shiftRight w j])

theorem val_sum_univ (f : Fin 8 → ZMod 2) :
    (∑ j : Fin 8, f j).val = (∑ j : Fin 8, (f j).val) % 2 := by
  classical
  have h : ∀ s : Finset (Fin 8), (∑ j ∈ s, f j).val = (∑ j ∈ s, (f j).val) % 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ZMod.val_add, ih]
        rw [Nat.add_mod_mod]
  simpa using h Finset.univ

theorem sum_mod_two {ι : Type*} (s : Finset ι) (a : ι → Nat) :
    (∑ i ∈ s, a i % 2) % 2 = (∑ i ∈ s, a i) % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      rw [Nat.mod_add_mod, ← Nat.add_mod_mod, ih, Nat.add_mod_mod]

theorem val_mulVec (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (v : V) (i : Fin 8) :
    ((M *ᵥ v) i).val = (∑ j : Fin 8, (M i j).val * (v j).val) % 2 := by
  rw [Matrix.mulVec_apply_eq_sum, val_sum_univ]
  rw [show (∑ j : Fin 8, (M i j * v j).val) =
        ∑ j : Fin 8, ((M i j).val * (v j).val % 2) by
      apply Finset.sum_congr rfl
      intro j _
      rw [ZMod.val_mul]]
  rw [sum_mod_two]

@[expose] def bitRow (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (mask : Nat) : Nat :=
  ∑ i : Fin 8, ((∑ j : Fin 8, (M i j).val * ((mask >>> (j : Nat)) % 2)) % 2) <<< (i : Nat)

theorem bitRow_bitmask (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (v : V) :
    bitRow M (bitmask v) = bitmask (M *ᵥ v) := by
  conv_rhs => rw [bitmask]
  unfold bitRow
  apply Finset.sum_congr rfl
  intro i _
  rw [val_mulVec]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [bitmask_shiftRight v j]

@[expose] def bitStep (l : Fin 2 × Bool) (mask : Nat) : Nat :=
  bitRow (spinLetterMatrix l) mask

@[expose] def bitWord (w : List (Fin 2 × Bool)) (mask : Nat) : Nat :=
  w.foldr bitStep mask

theorem bitWord_bitmask (w : List (Fin 2 × Bool)) (v : V) :
    bitWord w (bitmask v) = bitmask (evalSpinWordV w v) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
      change bitStep l (bitWord w (bitmask v)) = bitmask (spinStep l (evalSpinWordV w v))
      rw [ih]
      simpa [bitStep, spinStep] using
        bitRow_bitmask (spinLetterMatrix l) (evalSpinWordV w v)

theorem bitmask_basis (e : Fin 8) : bitmask (basis e) = 1 <<< (e : Nat) := by
  unfold bitmask basis
  rw [Finset.sum_eq_single e]
  · simp [ZMod.val_one]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro he
    simp at he

end CFSG.RankThree.GF2n.Parrott