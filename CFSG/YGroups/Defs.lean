module

public import CFSG.Certificates.CosetEnumeration
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.YGroups

@[expose] def ngen (p q r : ℕ) : ℕ := 1 + p + q + r

@[expose] def yEdges (p q r : ℕ) : List (ℕ × ℕ) :=
  (if 0 < p then [(0, 1)] else []) ++ (if 0 < q then [(0, 1 + p)] else []) ++
    (if 0 < r then [(0, 1 + p + q)] else []) ++
    (List.range (p - 1)).map (fun j => (1 + j, 2 + j)) ++
    (List.range (q - 1)).map (fun j => (1 + p + j, 2 + p + j)) ++
    (List.range (r - 1)).map (fun j => (1 + p + q + j, 2 + p + q + j))

@[expose] def spiderWord (p q : ℕ) : List ℕ := [0, 1, 2, 0, 1 + p, 2 + p, 0, 1 + p + q, 2 + p + q]

@[expose] def pairExp (p q r s t : ℕ) : ℕ := if (s, t) ∈ yEdges p q r then 3 else 2

@[expose] def pairWord (p q r s t : ℕ) : List ℕ :=
  (List.replicate (pairExp p q r s t) [s, t]).flatten

@[expose] def yRels (p q r : ℕ) : List (List ℕ) :=
  (List.range (ngen p q r)).map (fun s => [s, s]) ++
    ((List.range (ngen p q r)).flatMap fun s =>
      ((List.range (ngen p q r)).filter (s < ·)).map fun t => pairWord p q r s t) ++
    (if 2 ≤ p ∧ 2 ≤ q ∧ 2 ≤ r then [(List.replicate 10 (spiderWord p q)).flatten] else [])

@[expose] def wordFG (n : ℕ) (w : List ℕ) : FreeGroup (Fin n) :=
  (w.map fun c => if h : c < n then FreeGroup.of ⟨c, h⟩ else 1).prod

@[expose] def yRelSet (p q r : ℕ) : Set (FreeGroup (Fin (ngen p q r))) :=
  {x | ∃ w ∈ yRels p q r, wordFG (ngen p q r) w = x}

abbrev YGroup (p q r : ℕ) : Type := PresentedGroup (yRelSet p q r)

@[expose] noncomputable def yGen (p q r : ℕ) (c : ℕ) : YGroup p q r :=
  if h : c < ngen p q r then PresentedGroup.of ⟨c, h⟩ else 1

@[expose] def shiftAt (t c : ℕ) : ℕ := if c ≤ t then c else c + 1

open CFSG.Certificates.CosetEnumeration

theorem yGen_of_lt {p q r c : ℕ} (h : c < ngen p q r) :
    yGen p q r c = PresentedGroup.of ⟨c, h⟩ := by
  simp [yGen, h]

theorem yGen_of_le {p q r c : ℕ} (h : ngen p q r ≤ c) : yGen p q r c = 1 := by
  simp [yGen, Nat.not_lt.mpr h]

theorem evalWord_yGen (p q r : ℕ) (w : List ℕ) :
    evalWord (yGen p q r) w = PresentedGroup.mk _ (wordFG (ngen p q r) w) := by
  induction w with
  | nil => simp [evalWord, wordFG]
  | cons c w ih =>
    rw [evalWord_cons, ih]
    simp only [wordFG, List.map_cons, List.prod_cons, map_mul]
    congr 1
    by_cases h : c < ngen p q r
    · simp [yGen, h, PresentedGroup.of]
    · simp [yGen, h]

theorem evalWord_yGen_of_mem {p q r : ℕ} {w : List ℕ} (hw : w ∈ yRels p q r) :
    evalWord (yGen p q r) w = 1 := by
  rw [evalWord_yGen]
  exact PresentedGroup.one_of_mem ⟨w, hw, rfl⟩

theorem square_mem_yRels {p q r s : ℕ} (hs : s < ngen p q r) : [s, s] ∈ yRels p q r := by
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl ⟨s, hs, rfl⟩)

theorem yGen_mul_self (p q r c : ℕ) : yGen p q r c * yGen p q r c = 1 := by
  by_cases hc : c < ngen p q r
  · have := evalWord_yGen_of_mem (square_mem_yRels (p := p) (q := q) (r := r) hc)
    simpa [evalWord] using this
  · simp [yGen_of_le (Nat.not_lt.mp hc)]

theorem yGen_inv (p q r c : ℕ) : (yGen p q r c)⁻¹ = yGen p q r c :=
  inv_eq_of_mul_eq_one_right (yGen_mul_self p q r c)

theorem closure_yGen (p q r : ℕ) :
    Subgroup.closure (yGen p q r '' Set.Iio (ngen p q r)) = ⊤ := by
  have : yGen p q r '' Set.Iio (ngen p q r) = Set.range (PresentedGroup.of (rels := yRelSet p q r)) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, (yGen_of_lt hc).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.2, yGen_of_lt c.2⟩
  rw [this]
  exact PresentedGroup.closure_range_of _

end CFSG.YGroups
