module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm

@[expose] def x0P : Perm (Fin 6) := swap 2 3 * swap 4 5

@[expose] def y0P : Perm (Fin 6) := swap 0 2 * swap 1 3 * swap 3 4 * swap 4 5

@[expose] def wordP : List Bool → Perm (Fin 6)
  | [] => 1
  | b :: w => (if b then y0P else x0P) * wordP w

@[expose] def tr0 : Fin 6 → Perm (Fin 6) :=
  ![1, swap 0 1 * swap 1 2 * swap 2 4 * swap 4 5, swap 0 2 * swap 1 3 * swap 3 4 * swap 4 5,
    swap 0 3 * swap 3 5 * swap 5 1 * swap 1 2, swap 0 4 * swap 4 5 * swap 5 3 * swap 3 1,
    swap 0 5 * swap 5 2 * swap 2 3 * swap 3 1]

@[expose] def tr1 : Fin 6 → Perm (Fin 6) :=
  ![1, 1, swap 1 2 * swap 2 4 * swap 4 5 * swap 5 3, swap 1 3 * swap 2 5, swap 1 4 * swap 3 5,
    swap 1 5 * swap 5 2 * swap 2 3 * swap 3 4]

@[expose] def tr2 : Fin 6 → Perm (Fin 6) :=
  ![1, 1, 1, swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, swap 2 5 * swap 3 4]

@[expose] def tr3 : Fin 6 → Perm (Fin 6) := ![1, 1, 1, 1, swap 3 4 * swap 4 5, swap 3 5 * swap 5 4]

@[expose] def wd0 : Fin 6 → List Bool :=
  ![[], [true, false, true, false, true], [true], [false, true], [true, false, true],
    [false, true, false, true]]

@[expose] def wd1 : Fin 6 → List Bool :=
  ![[], [], [false, true, true, false, true, true], [true, true, false, true, true], [true, true],
    [false, true, true]]

@[expose] def wd2 : Fin 6 → List Bool :=
  ![[], [], [], [false], [true, true, true, false, true, false, true, true, true, false, true],
    [false, true, true, true, false, true, false, true, true, true, false, true]]

@[expose] def wd3 : Fin 6 → List Bool :=
  ![[], [], [], [], [true, false, true, true, false, true, false, true, true, true, false, true, true, false],
    [false, true, false, true, true, true, false, true, false, true, true, false, true]]

@[expose] def fac (g : Perm (Fin 6)) : Perm (Fin 6) :=
  let u₀ := tr0 (g 0)
  let g₁ := u₀⁻¹ * g
  let u₁ := tr1 (g₁ 1)
  let g₂ := u₁⁻¹ * g₁
  let u₂ := tr2 (g₂ 2)
  let g₃ := u₂⁻¹ * g₂
  let u₃ := tr3 (g₃ 3)
  u₀ * u₁ * u₂ * u₃

set_option maxRecDepth 100000 in
theorem fac_eq : ∀ g : Perm (Fin 6), sign g = 1 → fac g = g := by
  unfold fac
  decide +kernel

set_option maxRecDepth 100000 in
theorem tr_eq_word : (∀ j, tr0 j = wordP (wd0 j)) ∧ (∀ j, tr1 j = wordP (wd1 j)) ∧
    (∀ j, tr2 j = wordP (wd2 j)) ∧ ∀ j, tr3 j = wordP (wd3 j) := by
  unfold tr0 tr1 tr2 tr3 wd0 wd1 wd2 wd3 wordP
  decide +kernel

theorem wordP_mem (w : List Bool) :
    wordP w ∈ Subgroup.closure ({x0P, y0P} : Set (Perm (Fin 6))) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    cases b
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem alternatingGroup_le_closure :
    alternatingGroup (Fin 6) ≤ Subgroup.closure ({x0P, y0P} : Set (Perm (Fin 6))) := by
  intro g hg
  have h := fac_eq g (mem_alternatingGroup.mp hg)
  obtain ⟨h0, h1, h2, h3⟩ := tr_eq_word
  rw [← h]
  unfold fac
  simp only
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · rw [h0]; exact wordP_mem _
  · rw [h1]; exact wordP_mem _
  · rw [h2]; exact wordP_mem _
  · rw [h3]; exact wordP_mem _

end CFSG.Quasithin.A6Fin
