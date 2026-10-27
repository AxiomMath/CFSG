module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameCoord
public import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly
open scoped Matrix

@[expose] def stdY0 : Fin 5 → ZMod 3 := ![1, 1, 0, 0, 0]

@[expose] def stdB30 : Fin 5 → ZMod 3 := ![1, 2, 0, 0, 0]

@[expose] def stdB20 : Fin 5 → ZMod 3 := ![1, 0, 1, 0, 0]

@[expose] def stdWord : List (Fin 5 → ZMod 3) → (Fin 5 → ZMod 3) → (Fin 5 → ZMod 3)
  | [], c => c
  | r :: l, c => stdWord l (stdRefl r c)

theorem stdY0_eq : stdY0 = Pi.single (0 : Fin 5) 1 + Pi.single (1 : Fin 5) 1 := by
  decide +kernel

@[expose] def stdT30 : List (Fin 5 → ZMod 3) :=
  [
    ![0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 2],
    ![0, 0, 0, 2, 1],
    ![0, 0, 0, 2, 2],
    ![0, 0, 1, 0, 1],
    ![0, 0, 1, 0, 2],
    ![0, 0, 1, 1, 0],
    ![0, 0, 1, 2, 0],
    ![0, 0, 2, 0, 1],
    ![0, 0, 2, 0, 2],
    ![0, 0, 2, 1, 0],
    ![0, 0, 2, 2, 0],
    ![1, 2, 0, 0, 0],
    ![1, 2, 1, 1, 1],
    ![1, 2, 1, 1, 2],
    ![1, 2, 1, 2, 1],
    ![1, 2, 1, 2, 2],
    ![1, 2, 2, 1, 1],
    ![1, 2, 2, 1, 2],
    ![1, 2, 2, 2, 1],
    ![1, 2, 2, 2, 2],
    ![2, 1, 0, 0, 0],
    ![2, 1, 1, 1, 1],
    ![2, 1, 1, 1, 2],
    ![2, 1, 1, 2, 1],
    ![2, 1, 1, 2, 2],
    ![2, 1, 2, 1, 1],
    ![2, 1, 2, 1, 2],
    ![2, 1, 2, 2, 1],
    ![2, 1, 2, 2, 2],
  ]

@[expose] def stdT20 : List (Fin 5 → ZMod 3) :=
  [
    ![0, 1, 0, 0, 1],
    ![0, 1, 0, 0, 2],
    ![0, 1, 0, 1, 0],
    ![0, 1, 0, 2, 0],
    ![0, 1, 1, 0, 0],
    ![0, 1, 2, 0, 0],
    ![1, 0, 0, 0, 1],
    ![1, 0, 0, 0, 2],
    ![1, 0, 0, 1, 0],
    ![1, 0, 0, 2, 0],
    ![1, 0, 1, 0, 0],
    ![1, 0, 2, 0, 0],
    ![2, 2, 1, 1, 1],
    ![2, 2, 1, 1, 2],
    ![2, 2, 1, 2, 1],
    ![2, 2, 1, 2, 2],
    ![2, 2, 2, 1, 1],
    ![2, 2, 2, 1, 2],
    ![2, 2, 2, 2, 1],
    ![2, 2, 2, 2, 2],
  ]

@[expose] def stdW30 : List (List (Fin 5 → ZMod 3)) :=
  [
    [![1, 2, 1, 2, 2], ![1, 2, 2, 2, 2]],
    [![1, 2, 1, 2, 1], ![1, 2, 2, 2, 1]],
    [![1, 2, 1, 1, 2], ![1, 2, 2, 1, 2]],
    [![1, 2, 1, 1, 1], ![1, 2, 2, 1, 1]],
    [![1, 2, 2, 1, 2], ![1, 2, 2, 2, 2]],
    [![1, 2, 2, 1, 1], ![1, 2, 2, 2, 1]],
    [![1, 2, 2, 2, 1], ![1, 2, 2, 2, 2]],
    [![1, 2, 2, 1, 1], ![1, 2, 2, 1, 2]],
    [![1, 2, 1, 1, 2], ![1, 2, 1, 2, 2]],
    [![1, 2, 1, 1, 1], ![1, 2, 1, 2, 1]],
    [![1, 2, 1, 2, 1], ![1, 2, 1, 2, 2]],
    [![1, 2, 1, 1, 1], ![1, 2, 1, 1, 2]],
    [],
    [![1, 2, 0, 0, 0], ![1, 2, 2, 2, 2]],
    [![1, 2, 0, 0, 0], ![1, 2, 2, 2, 1]],
    [![1, 2, 0, 0, 0], ![1, 2, 2, 1, 2]],
    [![1, 2, 0, 0, 0], ![1, 2, 2, 1, 1]],
    [![1, 2, 0, 0, 0], ![1, 2, 1, 2, 2]],
    [![1, 2, 0, 0, 0], ![1, 2, 1, 2, 1]],
    [![1, 2, 0, 0, 0], ![1, 2, 1, 1, 2]],
    [![1, 2, 0, 0, 0], ![1, 2, 1, 1, 1]],
    [![1, 2, 0, 0, 0]],
    [![1, 2, 1, 1, 1]],
    [![1, 2, 1, 1, 2]],
    [![1, 2, 1, 2, 1]],
    [![1, 2, 1, 2, 2]],
    [![1, 2, 2, 1, 1]],
    [![1, 2, 2, 1, 2]],
    [![1, 2, 2, 2, 1]],
    [![1, 2, 2, 2, 2]],
  ]

@[expose] def stdW20 : List (List (Fin 5 → ZMod 3)) :=
  [
    [![0, 0, 1, 0, 2], ![1, 2, 0, 0, 0]],
    [![0, 0, 1, 0, 1], ![1, 2, 0, 0, 0]],
    [![0, 0, 1, 2, 0], ![1, 2, 0, 0, 0]],
    [![0, 0, 1, 1, 0], ![1, 2, 0, 0, 0]],
    [![1, 2, 0, 0, 0]],
    [![0, 0, 1, 0, 1], ![0, 0, 1, 0, 2], ![1, 2, 0, 0, 0]],
    [![0, 0, 1, 0, 2]],
    [![0, 0, 1, 0, 1]],
    [![0, 0, 1, 2, 0]],
    [![0, 0, 1, 1, 0]],
    [],
    [![0, 0, 1, 0, 1], ![0, 0, 1, 0, 2]],
    [![0, 0, 1, 0, 1], ![1, 2, 1, 1, 2]],
    [![0, 0, 1, 0, 2], ![1, 2, 1, 1, 1]],
    [![0, 0, 1, 0, 1], ![1, 2, 1, 2, 2]],
    [![0, 0, 1, 0, 2], ![1, 2, 1, 2, 1]],
    [![1, 2, 1, 1, 1]],
    [![1, 2, 1, 1, 2]],
    [![1, 2, 1, 2, 1]],
    [![1, 2, 1, 2, 2]],
  ]

theorem stdT30_spec : ∀ c : Fin 5 → ZMod 3,
    c ⬝ᵥ c = 2 → c ⬝ᵥ stdY0 = 0 → c ∈ stdT30 := by
  decide +kernel

theorem stdT20_spec : ∀ c : Fin 5 → ZMod 3,
    c ⬝ᵥ c = 2 → c ⬝ᵥ stdY0 = 1 → c ∈ stdT20 ∨ c = -stdY0 := by
  decide +kernel

theorem stdT20_mem {c : Fin 5 → ZMod 3} (hc : c ⬝ᵥ c = 2) (hc1 : c ⬝ᵥ stdY0 = 1)
    (hne : c ≠ -stdY0) : c ∈ stdT20 := by
  rcases stdT20_spec c hc hc1 with h | h
  · exact h
  · exact absurd h hne

open scoped CFSG.Decide.Bounded in
theorem stdT30_norm : ∀ t ∈ stdT30, t ⬝ᵥ t = 2 ∧ t ⬝ᵥ stdY0 = 0 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdT20_norm : ∀ t ∈ stdT20, t ⬝ᵥ t = 2 ∧ t ⬝ᵥ stdY0 = 1 ∧ t ≠ -stdY0 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdW30_apply : ∀ t ∈ stdT30, ∃ l ∈ stdW30, stdWord l stdB30 = t := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdW30_roots : ∀ l ∈ stdW30, ∀ r ∈ l, r ∈ stdT30 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdW20_apply : ∀ t ∈ stdT20, ∃ l ∈ stdW20, stdWord l stdB20 = t := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdW20_roots : ∀ l ∈ stdW20, ∀ r ∈ l, r ∈ stdT30 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdT20_step : ∀ t ∈ stdT20,
    stdY0 - t ∈ stdT20 ∧ stdRefl t (stdY0 - t) = stdY0 := by
  decide +kernel

end CFSG.StandardType.E6QTwo

end
