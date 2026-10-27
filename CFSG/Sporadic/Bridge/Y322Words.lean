module

public import CFSG.Certificates.WordPresentation
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Bridge.Y322

open CFSG.Certificates

@[expose] def edges : List (Fin 8 × Fin 8) :=
  [(0, 1), (1, 2), (2, 3), (0, 4), (4, 5), (0, 6), (6, 7)]

@[expose] def exponent (i j : Fin 8) : ℕ := if (i, j) ∈ edges ∨ (j, i) ∈ edges then 3 else 2

@[expose] def pairWord (i j : Fin 8) (k : ℕ) : List (Fin 8 × Bool) :=
  (List.replicate k [(i, true), (j, true)]).flatten

@[expose] def spiderWord : List (Fin 8 × Bool) :=
  (List.replicate 10 [(0, true), (1, true), (2, true), (0, true), (4, true), (5, true), (0, true),
    (6, true), (7, true)]).flatten

@[expose] def words : List (List (Fin 8 × Bool)) :=
  (List.finRange 8).map (fun i => [(i, true), (i, true)]) ++
    ((List.finRange 8).flatMap fun i =>
      ((List.finRange 8).filter fun j => decide (i < j)).map fun j => pairWord i j (exponent i j)) ++
    [spiderWord]

@[expose] def f1Word : List (Fin 8 × Bool) :=
  (List.replicate 9 [(0, true), (1, true), (2, true), (3, true), (4, true), (5, true),
    (6, true)]).flatten

@[expose] def f2Word : List (Fin 8 × Bool) :=
  (List.replicate 9 [(0, true), (1, true), (2, true), (3, true), (6, true), (7, true),
    (4, true)]).flatten

variable {G : Type*} [Group G]

theorem relations_iff (s : Fin 8 → G) :
    (∀ w ∈ words, signedProd s w = 1) ↔
      (∀ i, s i * s i = 1) ∧ (∀ i j, i < j → (s i * s j) ^ exponent i j = 1) ∧
        (s 0 * s 1 * s 2 * s 0 * s 4 * s 5 * s 0 * s 6 * s 7) ^ 10 = 1 := by
  simp only [words, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
    List.mem_finRange, true_and, List.mem_singleton, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
    · have := h _ (Or.inl (Or.inl ⟨i, rfl⟩))
      simpa [signedProd] using this
    · have := h _ (Or.inl (Or.inr ⟨i, j, hij, rfl⟩))
      rw [pairWord, signedProd_replicate] at this
      simpa [signedProd] using this
    · have := h _ (Or.inr rfl)
      rw [spiderWord, signedProd_replicate] at this
      simpa [signedProd, mul_assoc] using this
  · rintro ⟨h1, h2, h3⟩ w hw
    rcases hw with (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩) | rfl
    · simpa [signedProd] using h1 i
    · rw [pairWord, signedProd_replicate]
      simpa [signedProd] using h2 i j hij
    · rw [spiderWord, signedProd_replicate]
      simpa [signedProd, mul_assoc] using h3

theorem signedProd_f1Word (s : Fin 8 → G) :
    signedProd s f1Word = (s 0 * s 1 * s 2 * s 3 * s 4 * s 5 * s 6) ^ 9 := by
  rw [f1Word, signedProd_replicate]
  simp [signedProd, mul_assoc]

theorem signedProd_f2Word (s : Fin 8 → G) :
    signedProd s f2Word = (s 0 * s 1 * s 2 * s 3 * s 6 * s 7 * s 4) ^ 9 := by
  rw [f2Word, signedProd_replicate]
  simp [signedProd, mul_assoc]

def CentralWord : Prop :=
  ∀ {G : Type} [Group G] (s : Fin 8 → G), (∀ w ∈ words, signedProd s w = 1) →
    signedProd s f1Word = signedProd s f2Word ∧ signedProd s f1Word ^ 2 = 1 ∧
      ∀ i, Commute (s i) (signedProd s f1Word)

end CFSG.Sporadic.Bridge.Y322
