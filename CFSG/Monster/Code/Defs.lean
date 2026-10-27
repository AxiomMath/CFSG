module

public import CFSG.Monster.Code.F4
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster.Code

open F4

@[expose] def coord (r : Fin 4) (j : Fin 6) : Fin 24 := ⟨r + 4 * j, by omega⟩

@[expose] def row (i : Fin 24) : Fin 4 := ⟨i % 4, by omega⟩

@[expose] def col (i : Fin 24) : Fin 6 := ⟨i / 4, by omega⟩

@[simp] theorem row_coord (r : Fin 4) (j : Fin 6) : row (coord r j) = r := by
  ext; simp only [row, coord]; omega

@[simp] theorem col_coord (r : Fin 4) (j : Fin 6) : col (coord r j) = j := by
  ext; simp only [col, coord]; omega

@[simp] theorem coord_row_col (i : Fin 24) : coord (row i) (col i) = i := by
  ext; simp only [row, col, coord]; omega

theorem coord_injective {r r' : Fin 4} {j j' : Fin 6} (h : coord r j = coord r' j') :
    r = r' ∧ j = j' :=
  ⟨by simpa using congrArg row h, by simpa using congrArg col h⟩

@[expose] def v₁ : Fin 6 → F4 := ![1, 0, 0, 1, ᾱ, α]

@[expose] def v₂ : Fin 6 → F4 := ![0, 1, 0, 1, α, ᾱ]

@[expose] def v₃ : Fin 6 → F4 := ![0, 0, 1, 1, 1, 1]

@[expose] def H₆ : Submodule F4 (Fin 6 → F4) := Submodule.span F4 {v₁, v₂, v₃}

private theorem systematic : ∀ a b c : F4,
    a • v₁ + b • v₂ + c • v₃ = (a • v₁ + b • v₂ + c • v₃) 0 • v₁ +
      (a • v₁ + b • v₂ + c • v₃) 1 • v₂ + (a • v₁ + b • v₂ + c • v₃) 2 • v₃ := by
  decide

theorem mem_H₆_iff (y : Fin 6 → F4) : y ∈ H₆ ↔ y = y 0 • v₁ + y 1 • v₂ + y 2 • v₃ := by
  constructor
  · intro hy
    obtain ⟨a, z, hz, rfl⟩ := Submodule.mem_span_insert.1 hy
    obtain ⟨b, c, rfl⟩ := Submodule.mem_span_pair.1 hz
    simpa only [add_assoc] using systematic a b c
  · intro hy
    rw [hy, H₆]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_) <;> simp

instance : DecidablePred (· ∈ H₆) := fun y => decidable_of_iff _ (mem_H₆_iff y).symm

theorem v₁_mem : v₁ ∈ H₆ := by decide
theorem v₂_mem : v₂ ∈ H₆ := by decide
theorem v₃_mem : v₃ ∈ H₆ := by decide

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

@[expose] def hexProj (x : Fin 24 → ZMod 2) : Fin 6 → F4 := fun j =>
  algebraMap (ZMod 2) F4 (x (coord 1 j)) + α * algebraMap (ZMod 2) F4 (x (coord 2 j)) +
    ᾱ * algebraMap (ZMod 2) F4 (x (coord 3 j))

@[expose] def topParity (x : Fin 24 → ZMod 2) : ZMod 2 := ∑ j, x (coord 0 j)

theorem hexProj_add (x y : Fin 24 → ZMod 2) : hexProj (x + y) = hexProj x + hexProj y := by
  funext j; simp only [hexProj, Pi.add_apply, map_add]; ring

theorem hexProj_zero : hexProj 0 = 0 := by
  funext j; simp [hexProj]

theorem topParity_add (x y : Fin 24 → ZMod 2) :
    topParity (x + y) = topParity x + topParity y := by
  simp [topParity, Finset.sum_add_distrib]

@[expose] def C : Submodule (ZMod 2) (Fin 24 → ZMod 2) where
  carrier := {x | hexProj x ∈ H₆ ∧ ∀ j, ∑ r, x (coord r j) = topParity x}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by rw [hexProj_add]; exact H₆.add_mem hx hy, fun j => ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, topParity_add, hx' j, hy' j]
  zero_mem' := ⟨by rw [hexProj_zero]; exact H₆.zero_mem, fun j => by simp [topParity]⟩
  smul_mem' := by
    intro c x hx
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul]
      exact ⟨by rw [hexProj_zero]; exact H₆.zero_mem, fun j => by simp [topParity]⟩
    · rwa [one_smul]

theorem mem_C_iff (x : Fin 24 → ZMod 2) :
    x ∈ C ↔ hexProj x ∈ H₆ ∧ ∀ j, ∑ r, x (coord r j) = topParity x := Iff.rfl

instance : DecidablePred (· ∈ C) := fun x => decidable_of_iff _ (mem_C_iff x).symm

@[expose] def Ω : Fin 24 → ZMod 2 := fun _ => 1

@[expose] def ωInf : Fin 24 → ZMod 2 := fun i => if row i = 0 then 1 else 0

@[expose] def ω (j : Fin 6) : Fin 24 → ZMod 2 := fun i => if col i = j then 1 else 0

@[expose] def γ (j : Fin 6) : Fin 24 → ZMod 2 := Pi.single (coord 0 j) 1

@[expose] def g (j : Fin 6) : Fin 24 → ZMod 2 := ω j + ωInf

@[expose] def lCol (z : F4) : Fin 4 → ZMod 2 :=
  if z = 0 then ![0, 0, 0, 0] else if z = 1 then ![0, 0, 1, 1]
  else if z = α then ![0, 1, 0, 1] else ![0, 1, 1, 0]

theorem lCol_add : ∀ z w : F4, lCol (z + w) = lCol z + lCol w := by decide

theorem lCol_zero : lCol 0 = 0 := by decide

@[expose] def l : (Fin 6 → F4) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun y i := lCol (y (col i)) (row i)
  map_add' y y' := by funext i; simp [lCol_add]
  map_smul' c y := by
    rcases zmod2_cases c with rfl | rfl
    · funext i; simp [lCol_zero]
    · simp

theorem l_apply (y : Fin 6 → F4) (i : Fin 24) : l y i = lCol (y (col i)) (row i) := rfl

theorem l_apply_coord (y : Fin 6 → F4) (r : Fin 4) (j : Fin 6) :
    l y (coord r j) = lCol (y j) r := by simp [l_apply]

private theorem lCol_hex : ∀ z : F4, algebraMap (ZMod 2) F4 (lCol z 1) +
    α * algebraMap (ZMod 2) F4 (lCol z 2) + ᾱ * algebraMap (ZMod 2) F4 (lCol z 3) = z := by
  decide

theorem hexProj_l (y : Fin 6 → F4) : hexProj (l y) = y := by
  funext j; simp only [hexProj, l_apply_coord, lCol_hex]

@[expose] def G : Submodule (ZMod 2) (Fin 24 → ZMod 2) := Submodule.span (ZMod 2) (Set.range g)

@[expose] def H : Submodule (ZMod 2) (Fin 24 → ZMod 2) := (H₆.restrictScalars (ZMod 2)).map l

theorem mem_H_iff (x : Fin 24 → ZMod 2) : x ∈ H ↔ ∃ y ∈ H₆, l y = x := Iff.rfl

@[expose] def B : Fin 12 → Fin 24 → ZMod 2 :=
  ![g 0, g 1, g 2, g 3, g 4, g 5, l v₁, l (α • v₁), l v₂, l (α • v₂), l v₃, l (α • v₃)]

end CFSG.Monster.Code
