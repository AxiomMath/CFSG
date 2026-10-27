
module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Sporadic.Schreier.Co3Arrays

public noncomputable section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3Monomials : List (ℕ × ℕ) :=
  (List.range 22).flatMap fun i => (List.range (22 - i)).map fun t => (i, i + t)

theorem co3Monomials_pairIdx : co3Monomials.length = 253 ∧
    ∀ i < 22, ∀ j < 22, i ≤ j → co3Monomials[pairIdx22 i j]? = some (i, j) := by
  decide +kernel

abbrev Co3V : Type := Fin 22 → ZMod 2

@[expose] def co3Coef (t : ℕ) (i j : ℕ) : ZMod 2 := if t.testBit (pairIdx22 i j) then 1 else 0

@[expose] def co3Quad (t : ℕ) (v : Co3V) : ZMod 2 :=
  ∑ i : Fin 22, ∑ j : Fin 22, if i ≤ j then co3Coef t i j * v i * v j else 0

@[expose] def co3Form (r : ℕ) : Co3V → ZMod 2 := co3Quad (co3FormWord r)

@[expose] def co3X : Set (Co3V → ZMod 2) := {q | ∃ r < 276, co3Form r = q}

@[expose] def co3FinList (n : ℕ) (hn : 0 < n) (b : List ℕ) : List (Fin n) :=
  b.map fun x => ⟨x % n, Nat.mod_lt _ hn⟩

@[expose] def co3Chain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3ChainArrs co3ChainGenCount
    (by rw [co3ChainArrs, co3Field276, Array.size_ofFn]; decide)
    (co3FinList 276 (by decide) co3ChainBase) (by decide)
    (wordsArr co3ChainGenCount co3ChainStrongCount co3ChainDerivations)

@[expose] def co3CoprimeChain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3CoprimeArrs co3CoprimeGenCount
    (by rw [co3CoprimeArrs, co3Field276, Array.size_ofFn]; decide)
    (co3FinList 276 (by decide) co3CoprimeBase) (by decide)
    (wordsArr co3CoprimeGenCount co3CoprimeStrongCount co3CoprimeDerivations)

@[expose] def co3StrongPerm (j : ℕ) : Equiv.Perm (Fin 276) := permOfArr 276 co3ChainArrs[j]!

@[expose] def co3GenPerm (k : ℕ) : Equiv.Perm (Fin 276) := co3StrongPerm k

@[expose] def co3P : Subgroup (Equiv.Perm (Fin 276)) := co3Chain.originalSubgroup

@[expose] def co3WordValue : Equiv.Perm (Fin 276) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 2 => co3GenPerm h) (toLetters 2 co3CoprimeWord)

@[expose] def co3C0 : Equiv.Perm (Fin 276) := co3GenPerm 0

@[expose] def co3C1 : Equiv.Perm (Fin 276) := co3WordValue⁻¹ * co3GenPerm 1 * co3WordValue

@[expose] def co3C : Subgroup (Equiv.Perm (Fin 276)) := Subgroup.closure {co3C0, co3C1}

@[expose] def co3Point : Fin 276 := 0

@[expose] def co3H0 : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure {g | ∃ j ∈ co3StabIdx, co3StrongPerm j = g}

@[expose] def co3Pt (x : ℕ) : Fin 276 := ⟨x % 276, Nat.mod_lt _ (by decide)⟩

@[expose] def co3Merges : List (Fin 276 × List (Fin 2 × Fin 276 × Fin 276)) :=
  [(co3Pt co3MergeRep, co3MergeList.map fun m =>
    (⟨m.1 % 2, Nat.mod_lt _ (by decide)⟩, co3Pt m.2.1, co3Pt m.2.2))]

theorem co3ChainArrs_size : co3ChainArrs.size = 14 := by
  rw [co3ChainArrs, co3Field276, Array.size_ofFn]; decide

theorem co3CoprimeArrs_size : co3CoprimeArrs.size = 14 := by
  rw [co3CoprimeArrs, co3Field276, Array.size_ofFn]; decide

theorem co3_getElem!_map {f : Array ℕ → Array ℕ} {S : Array (Array ℕ)} {j : ℕ}
    (hj : j < S.size) : (S.map f)[j]! = f S[j]! := by
  rw [getElem!_pos (S.map f) j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem co3ChainArrs_get {j : ℕ} (hj : j < 14) : co3ChainArrs[j]! = co3Arr276 j := by
  rw [co3ChainArrs, co3Field276, getElem!_pos _ j (by simp [co3Lines276]; omega),
    Array.getElem_ofFn]
  simp [co3Lines276]

theorem co3CoprimeArrs_get {j : ℕ} (hj : j < 14) : co3CoprimeArrs[j]! = co3Arr276 (14 + j) := by
  rw [co3CoprimeArrs, co3Field276, getElem!_pos _ j (by simp [co3Lines276]; omega),
    Array.getElem_ofFn]
  simp [co3Lines276]

end CFSG.Sporadic.Schreier.Co3
