module

public import CFSG.ClassicalInvolution.Q3.AE.Group
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace Certificates.AE117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

@[expose] def inPi (x : Wr n) : Bool := decide (x = 1) || decide (x = allOnes n)

@[expose] def eqPi (x y : Wr n) : Bool := decide (x = y) || decide (x = y * allOnes n)

@[expose] def ord5Pi (x : Wr n) : Bool := !inPi x && inPi (x ^ 5)

@[expose] def indL (s : List (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ s then 1 else 0

@[expose] def indF (α : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ α then 1 else 0

@[expose] def memLC (a₀ a₁ a₂ a₃ : Fin n) (b : Bool) : List (Wr n) :=
  let d₁ := Equiv.swap a₀ a₁ * Equiv.swap a₂ a₃
  let d₂ := Equiv.swap a₀ a₂ * Equiv.swap a₁ a₃
  let d₃ := Equiv.swap a₀ a₃ * Equiv.swap a₁ a₂
  if b then
    [⟨indL [], 1⟩, ⟨indL [a₀, a₁, a₂, a₃], 1⟩, ⟨indL [a₀, a₂], d₁⟩, ⟨indL [a₁, a₃], d₁⟩,
      ⟨indL [a₀, a₃], d₂⟩, ⟨indL [a₁, a₂], d₂⟩, ⟨indL [a₀, a₁], d₃⟩, ⟨indL [a₂, a₃], d₃⟩]
  else
    [⟨indL [], 1⟩, ⟨indL [a₀, a₁, a₂, a₃], 1⟩, ⟨indL [a₀, a₃], d₁⟩, ⟨indL [a₁, a₂], d₁⟩,
      ⟨indL [a₀, a₁], d₂⟩, ⟨indL [a₂, a₃], d₂⟩, ⟨indL [a₀, a₂], d₃⟩, ⟨indL [a₁, a₃], d₃⟩]

@[expose] def memAtL (α : Finset (Fin n)) (b : Bool) : List (Wr n) :=
  match α.sort (· ≤ ·) with
  | [a₀, a₁, a₂, a₃] => memLC a₀ a₁ a₂ a₃ b
  | _ => []

abbrev adjProp (n : ℕ) : Prop :=
  ∀ α ∈ (Finset.univ : Finset (Fin n)).powersetCard 4,
    ∀ α' ∈ (Finset.univ : Finset (Fin n)).powersetCard 4,
      ((α ∩ α').card = 3 ↔ ∃ b ∈ [true, false], ∃ b' ∈ [true, false], ∃ k ∈ memAtL α b,
        ∃ k' ∈ memAtL α' b', ord5Pi (k * k') = true)

@[expose] def adjCheck (n : ℕ) (_ : Unit) : Bool := decide (adjProp n)

@[expose] def evalG {G : Type*} [Group G] (gens : List G) (w : List ℕ) : G :=
  w.foldl (fun acc k =>
    acc * if k % 2 = 0 then gens.getD (k / 2) 1 else (gens.getD (k / 2) 1)⁻¹) 1

abbrev cocProp (g₁ g₂ : Equiv.Perm (Fin n)) (rels : List (List ℕ)) : Prop :=
  (∀ w ∈ rels, inPi (evalG [ofPerm g₁, ofPerm g₂] w) = true) ∧
    ∀ v₁ v₂ : Fin n → ZMod 2, ∑ i, v₁ i = 0 → ∑ i, v₂ i = 0 →
      (∀ w ∈ rels, inPi (evalG [ofPerm g₁ * ofVec v₁, ofPerm g₂ * ofVec v₂] w) = true) →
        ∃ u : Fin n → ZMod 2,
          eqPi (ofVec u * ofPerm g₁ * (ofVec u)⁻¹) (ofPerm g₁ * ofVec v₁) = true ∧
            eqPi (ofVec u * ofPerm g₂ * (ofVec u)⁻¹) (ofPerm g₂ * ofVec v₂) = true

abbrev genProp (g₁ g₂ : Equiv.Perm (Fin n)) (words : List (List ℕ)) : Prop :=
  ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
    ∃ w ∈ words, evalG [g₁, g₂] w = Equiv.swap a b * Equiv.swap b c

abbrev spanProp (n : ℕ) : Prop :=
  ∀ v : Fin n → ZMod 2, ∑ i, v i = 0 → v = 0 ∨ v = 1 ∨
    (∃ α ∈ (Finset.univ : Finset (Fin n)).powersetCard 4, v = indF α) ∨
      ∃ α ∈ (Finset.univ : Finset (Fin n)).powersetCard 4,
        ∃ α' ∈ (Finset.univ : Finset (Fin n)).powersetCard 4, v = indF α + indF α'

@[expose] def spanCheck (n : ℕ) (_ : Unit) : Bool := decide (spanProp n)

@[expose] def g₁₅ : Equiv.Perm (Fin 5) := List.formPerm [0, 1, 2]
@[expose] def g₂₅ : Equiv.Perm (Fin 5) := List.formPerm [0, 1, 2, 3, 4]
@[expose] def g₁₆ : Equiv.Perm (Fin 6) := List.formPerm [0, 1, 2]
@[expose] def g₂₆ : Equiv.Perm (Fin 6) := List.formPerm [1, 2, 3, 4, 5]
@[expose] def g₁₇ : Equiv.Perm (Fin 7) := List.formPerm [0, 1, 2]
@[expose] def g₂₇ : Equiv.Perm (Fin 7) := List.formPerm [2, 3, 4, 5, 6]

@[expose] def rels₅ : List (List ℕ) := [[0, 0, 0], [0, 3, 0, 3, 0, 3]]
@[expose] def rels₆ : List (List ℕ) := [[0, 0, 0], [0, 2, 0, 2, 0, 2, 0, 2]]
@[expose] def rels₇ : List (List ℕ) := [[0, 0, 0], [2, 2, 2, 2, 2]]

@[expose] def words₅ : List (List ℕ) :=
  [[0], [1], [0, 2, 1, 3], [2, 0, 3, 1], [3, 0, 2], [3, 1, 2], [1, 2, 0, 3], [2, 1, 3, 0],
    [3, 0, 2, 1], [0, 3, 1, 2], [2, 1], [0, 3], [2, 0, 3], [2, 1, 3], [3, 1, 2, 0], [1, 3, 0, 2],
    [0, 2, 0], [1, 3, 1], [1, 2], [3, 0]]

@[expose] def words₆ : List (List ℕ) :=
  [[0], [1], [2, 0, 3, 0], [1, 2, 1, 3], [3, 3, 1, 2, 1, 2], [3, 0, 3, 0, 2, 2], [3, 1, 2],
    [3, 0, 2], [2, 0, 3], [2, 1, 3], [2, 2, 0, 3, 0, 3], [2, 1, 2, 1, 3, 3], [3, 1, 2, 1],
    [0, 3, 0, 2], [2, 2, 0, 3, 3], [0, 3, 3, 0, 2], [1, 3, 3, 1, 3, 0, 3], [0, 2, 2, 0, 2, 1, 2],
    [1, 2, 2, 1, 3], [2, 0, 3, 3, 0], [0, 2, 0, 3], [2, 1, 3, 1], [0, 2, 2, 0, 3, 0, 3],
    [1, 3, 3, 1, 2, 1, 2], [3, 0, 2, 0], [1, 3, 1, 2], [0, 3, 1, 2, 2, 0], [1, 3, 0, 3, 1, 2],
    [3, 0, 2, 2, 0, 3, 0], [0, 2, 1, 2, 0, 2, 2], [2, 2, 1, 3, 1], [0, 2, 0, 3, 3],
    [1, 3, 1, 2, 2], [3, 3, 0, 2, 0], [0, 3, 0, 2, 2, 0, 3], [2, 1, 3, 3, 1, 2, 1],
    [0, 2, 1, 2, 0, 3], [1, 2, 0, 3, 3, 1], [2, 1, 3, 1, 2], [3, 0, 2, 0, 3]]

@[expose] def words₇ : List (List ℕ) :=
  [[0], [1], [2, 0, 3], [2, 1, 3], [2, 2, 0, 3, 3], [2, 2, 1, 3, 3], [3, 3, 0, 2, 2],
    [3, 3, 1, 2, 2], [3, 0, 2], [3, 1, 2], [2, 0, 3, 1], [0, 2, 1, 3], [2, 2, 0, 3, 3, 1],
    [0, 2, 2, 1, 3, 3], [3, 3, 0, 2, 2, 1], [0, 3, 3, 1, 2, 2], [3, 0, 2, 1], [0, 3, 1, 2],
    [2, 2, 0, 3, 1, 3], [2, 0, 2, 1, 3, 3], [3, 3, 0, 3, 3, 1, 3], [2, 0, 2, 2, 1, 2, 2],
    [3, 0, 2, 2, 1, 3], [2, 0, 3, 3, 1, 2], [3, 3, 0, 3, 1, 3, 3], [2, 2, 0, 2, 1, 2, 2],
    [3, 0, 3, 3, 1, 3, 3], [2, 2, 0, 2, 2, 1, 2], [3, 0, 3, 1, 2, 2], [3, 3, 0, 2, 1, 2],
    [2, 1, 3, 0], [1, 2, 0, 3], [2, 2, 1, 3, 3, 0], [1, 2, 2, 0, 3, 3], [3, 3, 1, 2, 2, 0],
    [1, 3, 3, 0, 2, 2], [3, 1, 2, 0], [1, 3, 0, 2], [2, 2, 1, 3, 0, 3], [2, 1, 2, 0, 3, 3],
    [3, 3, 1, 3, 3, 0, 3], [2, 1, 2, 2, 0, 2, 2], [3, 1, 2, 2, 0, 3], [2, 1, 3, 3, 0, 2],
    [3, 3, 1, 3, 0, 3, 3], [2, 2, 1, 2, 0, 2, 2], [3, 1, 3, 3, 0, 3, 3], [2, 2, 1, 2, 2, 0, 2],
    [3, 1, 3, 0, 2, 2], [3, 3, 1, 2, 0, 2], [0, 2, 2, 1, 3, 0, 3, 1], [0, 2, 1, 2, 0, 3, 3, 1],
    [0, 3, 3, 1, 3, 3, 0, 3, 1], [0, 2, 1, 2, 2, 0, 2, 2, 1], [0, 3, 1, 2, 2, 0, 3, 1],
    [0, 2, 1, 3, 3, 0, 2, 1], [0, 3, 3, 1, 3, 0, 3, 3, 1], [0, 2, 2, 1, 2, 0, 2, 2, 1],
    [0, 3, 1, 3, 3, 0, 3, 3, 1], [0, 2, 2, 1, 2, 2, 0, 2, 1], [0, 3, 1, 3, 0, 2, 2, 1],
    [0, 3, 3, 1, 2, 0, 2, 1], [0, 2, 1, 3, 3, 0, 2, 1, 2], [0, 3, 1, 3, 0, 2, 2, 1, 3],
    [0, 2, 2, 1, 2, 0, 2, 2, 1, 2, 2], [0, 3, 3, 1, 3, 3, 0, 3, 1, 3, 3],
    [0, 2, 2, 1, 2, 2, 0, 2, 1, 2, 2], [0, 3, 3, 1, 3, 0, 3, 3, 1, 3, 3],
    [0, 2, 1, 2, 0, 3, 3, 1, 2], [0, 3, 1, 2, 2, 0, 3, 1, 3]]

@[expose] def cocCheck₅ (_ : Unit) : Bool := decide (cocProp g₁₅ g₂₅ rels₅)
@[expose] def cocCheck₆ (_ : Unit) : Bool := decide (cocProp g₁₆ g₂₆ rels₆)
@[expose] def cocCheck₇ (_ : Unit) : Bool := decide (cocProp g₁₇ g₂₇ rels₇)
@[expose] def genCheck₅ (_ : Unit) : Bool := decide (genProp g₁₅ g₂₅ words₅)
@[expose] def genCheck₆ (_ : Unit) : Bool := decide (genProp g₁₆ g₂₆ words₆)
@[expose] def genCheck₇ (_ : Unit) : Bool := decide (genProp g₁₇ g₂₇ words₇)

end Certificates.AE117
