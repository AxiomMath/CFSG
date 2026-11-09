module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType

@[expose] def ggE7Refl (i : Fin 7) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  1 - Matrix.of fun a b => if a = i then ((CartanMatrix.E 7 i b : ℤ) : ZMod 3) else 0

@[expose] def ggE7Prod (w : List (Fin 7)) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  (w.map ggE7Refl).prod

@[expose] def ggE7SylowGen : Fin 4 → Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![ggE7Prod [0, 2], ggE7Prod [5, 4],
    ggE7Prod [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3],
    ggE7Prod [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]]

@[expose] def ggE7SylowSet : Finset (Matrix (Fin 7) (Fin 7) (ZMod 3)) :=
  Finset.univ.image fun p : Fin 3 × Fin 3 × Fin 3 × Fin 3 =>
    ggE7SylowGen 0 ^ (p.1 : ℕ) * ggE7SylowGen 1 ^ (p.2.1 : ℕ) * ggE7SylowGen 2 ^ (p.2.2.1 : ℕ) *
      ggE7SylowGen 3 ^ (p.2.2.2 : ℕ)

theorem ggE7SylowSet_card : ggE7SylowSet.card = 81 := by
  decide +kernel

theorem ggE7SylowSet_one_mem : (1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ ggE7SylowSet := by
  decide +kernel

private def decEqMat7Fast : DecidableEq (Matrix (Fin 7) (Fin 7) (ZMod 3)) := fun A B =>
  decidable_of_iff (((List.finRange 7).all fun i => (List.finRange 7).all fun j =>
      decide (A i j = B i j)) = true) (by
    simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies]
    exact ⟨fun h => Matrix.ext h, fun h i j => h ▸ rfl⟩)

private abbrev ggE7MulGenAt (j : Fin 4) : Prop := ∀ p : Fin 3 × Fin 3 × Fin 3 × Fin 3,
    ∃ a ∈ (Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3 × Fin 3)),
      ggE7SylowGen 0 ^ (a.1 : ℕ) * ggE7SylowGen 1 ^ (a.2.1 : ℕ) * ggE7SylowGen 2 ^ (a.2.2.1 : ℕ) *
          ggE7SylowGen 3 ^ (a.2.2.2 : ℕ) =
        ggE7SylowGen 0 ^ (p.1 : ℕ) * ggE7SylowGen 1 ^ (p.2.1 : ℕ) *
            ggE7SylowGen 2 ^ (p.2.2.1 : ℕ) * ggE7SylowGen 3 ^ (p.2.2.2 : ℕ) * ggE7SylowGen j

attribute [local instance high] decEqMat7Fast in
private theorem ggE7SylowSet_mul_gen_0 : ggE7MulGenAt 0 := by
  unfold ggE7MulGenAt
  decide +kernel

attribute [local instance high] decEqMat7Fast in
private theorem ggE7SylowSet_mul_gen_1 : ggE7MulGenAt 1 := by
  unfold ggE7MulGenAt
  decide +kernel

attribute [local instance high] decEqMat7Fast in
private theorem ggE7SylowSet_mul_gen_2 : ggE7MulGenAt 2 := by
  unfold ggE7MulGenAt
  decide +kernel

attribute [local instance high] decEqMat7Fast in
private theorem ggE7SylowSet_mul_gen_3 : ggE7MulGenAt 3 := by
  unfold ggE7MulGenAt
  decide +kernel

theorem ggE7SylowSet_mul_gen (x : Matrix (Fin 7) (Fin 7) (ZMod 3)) (hx : x ∈ ggE7SylowSet)
    (j : Fin 4) : x * ggE7SylowGen j ∈ ggE7SylowSet := by
  rw [ggE7SylowSet, Finset.mem_image] at hx ⊢
  obtain ⟨p, -, rfl⟩ := hx
  have h : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases h j with rfl | rfl | rfl | rfl
  exacts [ggE7SylowSet_mul_gen_0 p, ggE7SylowSet_mul_gen_1 p, ggE7SylowSet_mul_gen_2 p,
    ggE7SylowSet_mul_gen_3 p]

theorem ggE7SylowSet_noEichler (x : Matrix (Fin 7) (Fin 7) (ZMod 3)) (hx : x ∈ ggE7SylowSet)
    (h1 : x ≠ 1) : x * x + x + 1 ≠ 0 := by
  rw [ggE7SylowSet, Finset.mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  revert p
  decide +kernel

end CFSG.StandardType

end
