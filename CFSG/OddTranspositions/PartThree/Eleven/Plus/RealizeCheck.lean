module

public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.PermData
public import CFSG.RankThree.Native.F5MatrixArrays

public section

namespace CFSG.OddTranspositions.PartThree.PlusRealize

open CFSG.RankThree.Native
open Matrix

attribute [-instance] CFSG.RankThree.Native.fact_prime_five

def plusSquareVecs : Array (Array ℕ) :=
  #[
    #[0, 0, 0, 1],
    #[0, 0, 1, 0],
    #[0, 1, 0, 0],
    #[0, 1, 1, 1],
    #[0, 1, 1, 4],
    #[0, 1, 2, 1],
    #[0, 1, 2, 2],
    #[0, 1, 2, 3],
    #[0, 1, 2, 4],
    #[0, 1, 3, 1],
    #[0, 1, 3, 2],
    #[0, 1, 3, 3],
    #[0, 1, 3, 4],
    #[0, 1, 4, 1],
    #[0, 1, 4, 4],
    #[1, 0, 0, 0],
    #[1, 0, 1, 1],
    #[1, 0, 1, 4],
    #[1, 0, 2, 1],
    #[1, 0, 2, 2],
    #[1, 0, 2, 3],
    #[1, 0, 2, 4],
    #[1, 0, 3, 1],
    #[1, 0, 3, 2],
    #[1, 0, 3, 3],
    #[1, 0, 3, 4],
    #[1, 0, 4, 1],
    #[1, 0, 4, 4],
    #[1, 1, 0, 1],
    #[1, 1, 0, 4],
    #[1, 1, 1, 2],
    #[1, 1, 1, 3],
    #[1, 1, 2, 0],
    #[1, 1, 3, 0],
    #[1, 1, 4, 2],
    #[1, 1, 4, 3],
    #[1, 2, 0, 1],
    #[1, 2, 0, 2],
    #[1, 2, 0, 3],
    #[1, 2, 0, 4],
    #[1, 2, 1, 0],
    #[1, 2, 2, 0],
    #[1, 2, 3, 0],
    #[1, 2, 4, 0],
    #[1, 3, 0, 1],
    #[1, 3, 0, 2],
    #[1, 3, 0, 3],
    #[1, 3, 0, 4],
    #[1, 3, 1, 0],
    #[1, 3, 2, 0],
    #[1, 3, 3, 0],
    #[1, 3, 4, 0],
    #[1, 4, 0, 1],
    #[1, 4, 0, 4],
    #[1, 4, 1, 2],
    #[1, 4, 1, 3],
    #[1, 4, 2, 0],
    #[1, 4, 3, 0],
    #[1, 4, 4, 2],
    #[1, 4, 4, 3]]

def plusNonsquareVecs : Array (Array ℕ) :=
  #[
    #[0, 0, 1, 2],
    #[0, 0, 1, 3],
    #[1, 4, 0, 0],
    #[1, 4, 1, 1],
    #[1, 4, 2, 3],
    #[1, 4, 0, 3],
    #[1, 4, 2, 2],
    #[1, 4, 4, 1],
    #[1, 4, 1, 0],
    #[1, 4, 4, 0],
    #[1, 4, 1, 4],
    #[1, 4, 3, 3],
    #[1, 4, 0, 2],
    #[1, 4, 3, 2],
    #[1, 4, 4, 4],
    #[1, 1, 0, 0],
    #[1, 1, 4, 4],
    #[1, 1, 3, 2],
    #[1, 1, 0, 2],
    #[1, 1, 3, 3],
    #[1, 1, 1, 4],
    #[1, 1, 4, 0],
    #[1, 1, 1, 0],
    #[1, 1, 4, 1],
    #[1, 1, 2, 2],
    #[1, 1, 0, 3],
    #[1, 1, 2, 3],
    #[1, 1, 1, 1],
    #[0, 1, 4, 3],
    #[0, 1, 1, 2],
    #[0, 1, 1, 0],
    #[0, 1, 0, 3],
    #[0, 1, 1, 3],
    #[0, 1, 4, 2],
    #[0, 1, 0, 2],
    #[0, 1, 4, 0],
    #[1, 2, 2, 4],
    #[1, 2, 4, 3],
    #[1, 2, 1, 2],
    #[1, 2, 3, 1],
    #[1, 2, 4, 2],
    #[1, 2, 3, 4],
    #[1, 2, 2, 1],
    #[1, 2, 1, 3],
    #[1, 3, 1, 2],
    #[1, 3, 2, 4],
    #[1, 3, 3, 1],
    #[1, 3, 4, 3],
    #[1, 3, 2, 1],
    #[1, 3, 4, 2],
    #[1, 3, 1, 3],
    #[1, 3, 3, 4],
    #[1, 0, 4, 3],
    #[1, 0, 1, 2],
    #[1, 0, 1, 0],
    #[1, 0, 0, 3],
    #[1, 0, 1, 3],
    #[1, 0, 4, 2],
    #[1, 0, 0, 2],
    #[1, 0, 4, 0]]

@[expose] def Jv (v : Fin 4 → ZMod 5) : Fin 4 → ZMod 5 :=
  fun b => if b = 0 then v 0 else if b = 1 then v 1 else if b = 2 then v 2 else -v 3

@[expose] def reflMat (v : Fin 4 → ZMod 5) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  fun a b => (if a = b then 1 else 0) - 2 * (fiveForm 3 true v v)⁻¹ * v a * Jv v b

@[expose] def decode (v : Array ℕ) (a : Fin 4) : ZMod 5 := (v[a]! : ZMod 5)

@[expose] def reflArr (v : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun k =>
    (reflMat (decode v) ⟨(k : ℕ) / 4, by omega⟩ ⟨(k : ℕ) % 4, by omega⟩).val

theorem f5Mat_reflArr (v : Array ℕ) : f5Mat (reflArr v) = reflMat (decode v) := by
  ext a b
  simp only [f5Mat, Matrix.of_apply]
  have hk : 4 * (a : ℕ) + (b : ℕ) < (reflArr v).size := by simp [reflArr]; omega
  rw [getElem!_pos (reflArr v) _ hk]
  simp only [reflArr, Array.getElem_ofFn]
  have h1 : (⟨(4 * (a : ℕ) + (b : ℕ)) / 4, by omega⟩ : Fin 4) = a := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  have h2 : (⟨(4 * (a : ℕ) + (b : ℕ)) % 4, by omega⟩ : Fin 4) = b := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [h1, h2]
  exact ZMod.natCast_zmod_val _

@[expose] def vecA (π : Bool) (i : Fin 60) : Array ℕ :=
  (if π then plusSquareVecs else plusNonsquareVecs)[i]!

@[expose] def vecD (π : Bool) (i : Fin 60) : Fin 4 → ZMod 5 := decode (vecA π i)

@[expose] def MA (π : Bool) (i : Fin 60) : Array ℕ := reflArr (vecA π i)

@[expose] def TA (i j : Fin 60) : Fin 60 := Fin.ofNat 60 ((plusTable[i]!)[j]!)

@[expose, reducible] def signProp (π : Bool) : Prop :=
  ∀ i : Fin 60, fiveForm 3 true (vecD π i) (vecD π i) ≠ 0 ∧
    (IsSquare (fiveForm 3 true (vecD π i) (vecD π i)) ↔ π = true)

@[expose, reducible] def coverProp (π : Bool) : Prop :=
  ∀ v : Fin 4 → ZMod 5, fiveForm 3 true v v ≠ 0 →
    (IsSquare (fiveForm 3 true v v) ↔ π = true) →
    ∃ (i : Fin 60) (c : ZMod 5), c ≠ 0 ∧ v = c • vecD π i

@[expose, reducible] def matProp (M : Array (Array ℕ)) : Prop :=
  (∀ i : Fin 60, f5ValidA M[(i : ℕ)]! = true) ∧
  (∀ i : Fin 60, f5EqA (f5MulA M[(i : ℕ)]! M[(i : ℕ)]!) f5IdA = true) ∧
  (∀ i j : Fin 60,
    f5EqA (f5MulA (f5MulA M[(i : ℕ)]! M[(j : ℕ)]!) M[(i : ℕ)]!) M[(TA i j : ℕ)]! = true) ∧
  (∀ i j : Fin 60, i ≠ j → f5EqA M[(i : ℕ)]! M[(j : ℕ)]! = false)

def realizeCheck (_ : Unit := ()) : Bool :=
  let Mt : Array (Array ℕ) := (List.ofFn fun i : Fin 60 => MA true i).toArray
  let Mf : Array (Array ℕ) := (List.ofFn fun i : Fin 60 => MA false i).toArray
  decide (signProp true) && decide (signProp false) &&
  decide (matProp Mt) && decide (matProp Mf) &&
  decide (coverProp true) && decide (coverProp false)

theorem getElem_toArray_ofFn {n : ℕ} (f : Fin n → Array ℕ) (i : Fin n) :
    ((List.ofFn f).toArray)[(i : ℕ)]! = f i := by
  simp

theorem getElem_toArray_ofFn_MA (π : Bool) (i : Fin 60) :
    ((List.ofFn fun i : Fin 60 => MA π i).toArray)[(i : ℕ)]! = MA π i :=
  getElem_toArray_ofFn _ i

theorem sign_of_check (π : Bool) (h : realizeCheck () = true) : signProp π := by
  simp only [realizeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩
  cases π
  · exact h2
  · exact h1

theorem cover_of_check (π : Bool) (h : realizeCheck () = true) : coverProp π := by
  simp only [realizeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, h5⟩, h6⟩
  cases π
  · exact h6
  · exact h5

theorem matProp_of_check (π : Bool) (h : realizeCheck () = true) :
    matProp ((List.ofFn fun i : Fin 60 => MA π i).toArray) := by
  simp only [realizeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, _⟩, _⟩
  cases π
  · exact h4
  · exact h3

theorem validA_of_check (π : Bool) (h : realizeCheck () = true) (i : Fin 60) :
    f5ValidA (MA π i) = true := by
  have := (matProp_of_check π h).1 i
  rwa [getElem_toArray_ofFn_MA π i] at this

theorem inv_of_check (π : Bool) (h : realizeCheck () = true) (i : Fin 60) :
    f5EqA (f5MulA (MA π i) (MA π i)) f5IdA = true := by
  have := (matProp_of_check π h).2.1 i
  rwa [getElem_toArray_ofFn_MA π i] at this

theorem table_of_check (π : Bool) (h : realizeCheck () = true) (i j : Fin 60) :
    f5EqA (f5MulA (f5MulA (MA π i) (MA π j)) (MA π i)) (MA π (TA i j)) = true := by
  have := (matProp_of_check π h).2.2.1 i j
  rwa [getElem_toArray_ofFn_MA π i, getElem_toArray_ofFn_MA π j,
    getElem_toArray_ofFn_MA π (TA i j)] at this

theorem distinct_of_check (π : Bool) (h : realizeCheck () = true) {i j : Fin 60}
    (hij : i ≠ j) : f5EqA (MA π i) (MA π j) = false := by
  have := (matProp_of_check π h).2.2.2 i j hij
  rwa [getElem_toArray_ofFn_MA π i, getElem_toArray_ofFn_MA π j] at this

end CFSG.OddTranspositions.PartThree.PlusRealize
