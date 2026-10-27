module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08FullCoordsExc
public import CFSG.LocalAnalysis.StandardType.GGQ2S08PermLin
public import CFSG.Mathlib.Decide.Bounded
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG.StandardType.TestLin

open Matrix

abbrev E7G : Type := Vn 8 ≃ₗ[ZMod 3] Vn 8

@[expose] def e7Roots : List (Vn 8) := [![0, 0, 0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 0, 2, 1],
  ![0, 0, 0, 0, 0, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 2, 0], ![0, 0, 0, 0, 0, 2, 0, 1],
  ![0, 0, 0, 0, 0, 2, 1, 0], ![0, 0, 0, 0, 1, 0, 0, 2], ![0, 0, 0, 0, 1, 0, 2, 0],
  ![0, 0, 0, 0, 1, 2, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 1], ![0, 0, 0, 0, 2, 0, 1, 0],
  ![0, 0, 0, 0, 2, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 2], ![0, 0, 0, 1, 0, 0, 2, 0],
  ![0, 0, 0, 1, 0, 2, 0, 0], ![0, 0, 0, 1, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 1],
  ![0, 0, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 2, 0, 1, 0, 0], ![0, 0, 0, 2, 1, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 2], ![0, 0, 1, 0, 0, 0, 2, 0], ![0, 0, 1, 0, 0, 2, 0, 0],
  ![0, 0, 1, 0, 2, 0, 0, 0], ![0, 0, 1, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 1],
  ![0, 0, 2, 0, 0, 0, 1, 0], ![0, 0, 2, 0, 0, 1, 0, 0], ![0, 0, 2, 0, 1, 0, 0, 0],
  ![0, 0, 2, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 2], ![0, 1, 0, 0, 0, 0, 2, 0],
  ![0, 1, 0, 0, 0, 2, 0, 0], ![0, 1, 0, 0, 2, 0, 0, 0], ![0, 1, 0, 2, 0, 0, 0, 0],
  ![0, 1, 2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 1], ![0, 2, 0, 0, 0, 0, 1, 0],
  ![0, 2, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 0, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0, 0, 0],
  ![0, 2, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 2], ![1, 0, 0, 0, 0, 0, 2, 0],
  ![1, 0, 0, 0, 0, 2, 0, 0], ![1, 0, 0, 0, 2, 0, 0, 0], ![1, 0, 0, 2, 0, 0, 0, 0],
  ![1, 0, 2, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 2, 2, 2, 2], ![1, 1, 1, 2, 1, 2, 2, 2],
  ![1, 1, 1, 2, 2, 1, 2, 2], ![1, 1, 1, 2, 2, 2, 1, 2], ![1, 1, 1, 2, 2, 2, 2, 1],
  ![1, 1, 2, 1, 1, 2, 2, 2], ![1, 1, 2, 1, 2, 1, 2, 2], ![1, 1, 2, 1, 2, 2, 1, 2],
  ![1, 1, 2, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 1, 1, 2, 2], ![1, 1, 2, 2, 1, 2, 1, 2],
  ![1, 1, 2, 2, 1, 2, 2, 1], ![1, 1, 2, 2, 2, 1, 1, 2], ![1, 1, 2, 2, 2, 1, 2, 1],
  ![1, 1, 2, 2, 2, 2, 1, 1], ![1, 2, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 1, 1, 2, 2, 2],
  ![1, 2, 1, 1, 2, 1, 2, 2], ![1, 2, 1, 1, 2, 2, 1, 2], ![1, 2, 1, 1, 2, 2, 2, 1],
  ![1, 2, 1, 2, 1, 1, 2, 2], ![1, 2, 1, 2, 1, 2, 1, 2], ![1, 2, 1, 2, 1, 2, 2, 1],
  ![1, 2, 1, 2, 2, 1, 1, 2], ![1, 2, 1, 2, 2, 1, 2, 1], ![1, 2, 1, 2, 2, 2, 1, 1],
  ![1, 2, 2, 1, 1, 1, 2, 2], ![1, 2, 2, 1, 1, 2, 1, 2], ![1, 2, 2, 1, 1, 2, 2, 1],
  ![1, 2, 2, 1, 2, 1, 1, 2], ![1, 2, 2, 1, 2, 1, 2, 1], ![1, 2, 2, 1, 2, 2, 1, 1],
  ![1, 2, 2, 2, 1, 1, 1, 2], ![1, 2, 2, 2, 1, 1, 2, 1], ![1, 2, 2, 2, 1, 2, 1, 1],
  ![1, 2, 2, 2, 2, 1, 1, 1], ![2, 0, 0, 0, 0, 0, 0, 1], ![2, 0, 0, 0, 0, 0, 1, 0],
  ![2, 0, 0, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0, 0],
  ![2, 0, 1, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0], ![2, 1, 1, 1, 1, 2, 2, 2],
  ![2, 1, 1, 1, 2, 1, 2, 2], ![2, 1, 1, 1, 2, 2, 1, 2], ![2, 1, 1, 1, 2, 2, 2, 1],
  ![2, 1, 1, 2, 1, 1, 2, 2], ![2, 1, 1, 2, 1, 2, 1, 2], ![2, 1, 1, 2, 1, 2, 2, 1],
  ![2, 1, 1, 2, 2, 1, 1, 2], ![2, 1, 1, 2, 2, 1, 2, 1], ![2, 1, 1, 2, 2, 2, 1, 1],
  ![2, 1, 2, 1, 1, 1, 2, 2], ![2, 1, 2, 1, 1, 2, 1, 2], ![2, 1, 2, 1, 1, 2, 2, 1],
  ![2, 1, 2, 1, 2, 1, 1, 2], ![2, 1, 2, 1, 2, 1, 2, 1], ![2, 1, 2, 1, 2, 2, 1, 1],
  ![2, 1, 2, 2, 1, 1, 1, 2], ![2, 1, 2, 2, 1, 1, 2, 1], ![2, 1, 2, 2, 1, 2, 1, 1],
  ![2, 1, 2, 2, 2, 1, 1, 1], ![2, 2, 1, 1, 1, 1, 2, 2], ![2, 2, 1, 1, 1, 2, 1, 2],
  ![2, 2, 1, 1, 1, 2, 2, 1], ![2, 2, 1, 1, 2, 1, 1, 2], ![2, 2, 1, 1, 2, 1, 2, 1],
  ![2, 2, 1, 1, 2, 2, 1, 1], ![2, 2, 1, 2, 1, 1, 1, 2], ![2, 2, 1, 2, 1, 1, 2, 1],
  ![2, 2, 1, 2, 1, 2, 1, 1], ![2, 2, 1, 2, 2, 1, 1, 1], ![2, 2, 2, 1, 1, 1, 1, 2],
  ![2, 2, 2, 1, 1, 1, 2, 1], ![2, 2, 2, 1, 1, 2, 1, 1], ![2, 2, 2, 1, 2, 1, 1, 1],
  ![2, 2, 2, 2, 1, 1, 1, 1]]

@[expose] def e7Sorted : List (Vn 8) := [![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 2],
  ![0, 0, 0, 0, 0, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 2],
  ![0, 0, 0, 0, 0, 1, 2, 2], ![0, 0, 0, 0, 0, 2, 2, 2], ![0, 0, 0, 0, 1, 1, 1, 1],
  ![0, 0, 0, 0, 1, 1, 1, 2], ![0, 0, 0, 0, 1, 1, 2, 2], ![0, 0, 0, 0, 1, 2, 2, 2],
  ![0, 0, 0, 0, 2, 2, 2, 2], ![0, 0, 0, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 1, 2],
  ![0, 0, 0, 1, 1, 1, 2, 2], ![0, 0, 0, 1, 1, 2, 2, 2], ![0, 0, 0, 1, 2, 2, 2, 2],
  ![0, 0, 0, 2, 2, 2, 2, 2], ![0, 0, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1, 2],
  ![0, 0, 1, 1, 1, 1, 2, 2], ![0, 0, 1, 1, 1, 2, 2, 2], ![0, 0, 1, 1, 2, 2, 2, 2],
  ![0, 0, 1, 2, 2, 2, 2, 2], ![0, 0, 2, 2, 2, 2, 2, 2], ![0, 1, 1, 1, 1, 1, 1, 1],
  ![0, 1, 1, 1, 1, 1, 1, 2], ![0, 1, 1, 1, 1, 1, 2, 2], ![0, 1, 1, 1, 1, 2, 2, 2],
  ![0, 1, 1, 1, 2, 2, 2, 2], ![0, 1, 1, 2, 2, 2, 2, 2], ![0, 1, 2, 2, 2, 2, 2, 2],
  ![0, 2, 2, 2, 2, 2, 2, 2], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 2],
  ![1, 1, 1, 1, 1, 1, 2, 2], ![1, 1, 1, 1, 1, 2, 2, 2], ![1, 1, 1, 1, 2, 2, 2, 2],
  ![1, 1, 1, 2, 2, 2, 2, 2], ![1, 1, 2, 2, 2, 2, 2, 2], ![1, 2, 2, 2, 2, 2, 2, 2],
  ![2, 2, 2, 2, 2, 2, 2, 2]]

inductive E7Gen where
  | u
  | g (k : Fin 7)

@[expose] def E7word (u : E7G) : List E7Gen → E7G
  | [] => 1
  | .u :: l => u * E7word u l
  | .g k :: l => e7FullS k * E7word u l

inductive E7Verdict where
  | excl (word : List E7Gen) (k : Fin 7) (r : Vn 8)
  | tv (word : List E7Gen) (ct af : Vn 8)
  | rep
  | conj (word : List E7Gen)

structure E7Pat where
  c : Vn 8
  a : Vn 8
  hac : a ⬝ᵥ c = 2
  verdict : E7Verdict

@[expose] def E7Pat.u (p : E7Pat) : E7G := refl p.c p.a p.hac

@[expose] def e7RepC : Vn 8 := ![0, 0, 0, 0, 0, 0, 1, 1]

@[expose] def e7Rep : E7G := refl e7RepC e7RepC (by decide +kernel)

abbrev E7Eq (f g : E7G) : Prop := ∀ j, f (Pi.single j 1) = g (Pi.single j 1)

@[expose] def E7Pat.check (p : E7Pat) : Prop :=
  match p.verdict with
  | .excl word k r =>
      r ∈ e7Roots ∧
        (E7word p.u word e7FullX = e7FullX ∨ E7word p.u word e7FullX = -e7FullX) ∧
        (E7word p.u word * e7FullS k * (E7word p.u word)⁻¹) r ∉ e7Roots
  | .tv word ct af =>
      ct ≠ 0 ∧ af ≠ 0 ∧ af ⬝ᵥ ct = 0 ∧
        (∀ j, E7word p.u word (Pi.single j 1) = Pi.single j 1 + (af j) • ct)
  | .rep => E7Eq p.u e7Rep
  | .conj word => E7Eq (E7word 1 word * p.u * (E7word 1 word)⁻¹) e7Rep

@[expose] def e7DotLin (a : Vn 8) : Vn 8 →ₗ[ZMod 3] ZMod 3 :=
  ∑ j : Fin 8, a j • LinearMap.proj j

theorem e7DotLin_apply (a v : Vn 8) : e7DotLin a v = a ⬝ᵥ v := by
  simp [e7DotLin, dotProduct, LinearMap.proj]

@[expose] def e7TransvLin (c a : Vn 8) : Vn 8 →ₗ[ZMod 3] Vn 8 :=
  LinearMap.id + (e7DotLin a).smulRight c

theorem e7TransvLin_apply (c a v : Vn 8) :
    e7TransvLin c a v = v + (a ⬝ᵥ v) • c := by
  simp [e7TransvLin, e7DotLin_apply, LinearMap.smulRight_apply]

theorem isTransv_of_basis {g : E7G} {c a : Vn 8} (hc : c ≠ 0) (ha : a ≠ 0)
    (hac : a ⬝ᵥ c = 0)
    (h : ∀ j, g (Pi.single j 1) = Pi.single j 1 + (a j) • c) : IsTransv g := by
  refine ⟨c, a, hc, ha, hac, fun v => ?_⟩
  have hg : (g : Vn 8 →ₗ[ZMod 3] Vn 8) = e7TransvLin c a := by
    apply linearMap_eq_of_basis
    intro j
    rw [e7TransvLin_apply, dotProduct_single, mul_one]
    exact h j
  exact congrArg (fun f : Vn 8 →ₗ[ZMod 3] Vn 8 => f v) hg

theorem eq_of_E7Eq {f g : E7G} (h : E7Eq f g) : f = g := by
  apply LinearEquiv.ext
  intro v
  have h' : (f : Vn 8 →ₗ[ZMod 3] Vn 8) = (g : Vn 8 →ₗ[ZMod 3] Vn 8) :=
    linearMap_eq_of_basis h
  exact congrArg (fun φ : Vn 8 →ₗ[ZMod 3] Vn 8 => φ v) h'

open scoped CFSG.Decide.Bounded in
theorem e7FullS_maps_roots :
    ∀ k : Fin 7, ∀ s ∈ e7Roots, e7FullS k s ∈ e7Roots := by
  decide +kernel

theorem e7_closure_maps_roots {w : E7G}
    (hw : w ∈ Subgroup.closure (Set.range e7FullS)) :
    ∀ s ∈ e7Roots, w s ∈ e7Roots := by
  have hP : ∀ v ∈ Subgroup.closure (Set.range e7FullS),
      (∀ s ∈ e7Roots, v s ∈ e7Roots) ∧ (∀ s ∈ e7Roots, v⁻¹ s ∈ e7Roots) := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        refine ⟨e7FullS_maps_roots k, ?_⟩
        have hinv : (e7FullS k)⁻¹ = e7FullS k := by
          apply inv_eq_of_mul_eq_one_right
          simpa [e7FullS] using
            refl_mul_self (e7β k) (e7β k) (by fin_cases k <;> decide +kernel)
        intro s hs
        rw [hinv]
        exact e7FullS_maps_roots k s hs
    | one => refine ⟨?_, ?_⟩ <;> intro s hs <;> simpa using hs
    | mul x y _ _ ihx ihy =>
        refine ⟨?_, ?_⟩
        · intro s hs
          rw [LinearEquiv.mul_apply]
          exact ihx.1 (y s) (ihy.1 s hs)
        · intro s hs
          rw [_root_.mul_inv_rev, LinearEquiv.mul_apply]
          exact ihy.2 (x⁻¹ s) (ihx.2 s hs)
    | inv x _ ihx =>
        refine ⟨ihx.2, ?_⟩
        intro s hs
        simpa [inv_inv] using ihx.1 s hs
  exact (hP w hw).1

theorem E7word_mem {A : Subgroup E7G} {u : E7G} (hu : u ∈ A)
    (hg : ∀ k, e7FullS k ∈ A) (word : List E7Gen) : E7word u word ∈ A := by
  induction word with
  | nil => exact A.one_mem
  | cons x l ih =>
      cases x with
      | u => simpa [E7word] using A.mul_mem hu ih
      | g k => exact A.mul_mem (hg k) ih

theorem E7word_one_mem_closure (word : List E7Gen) :
    E7word 1 word ∈ Subgroup.closure (Set.range e7FullS) := by
  induction word with
  | nil => exact Subgroup.one_mem _
  | cons x l ih =>
      cases x with
      | u => simpa [E7word] using ih
      | g k => exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, rfl⟩) ih

@[expose] def e7PatList : List E7Pat := [
  { c := ![0, 0, 0, 0, 0, 0, 0, 1], a := ![0, 0, 0, 0, 0, 0, 0, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 1, 0, 0, 2] },
  { c := ![0, 0, 0, 0, 0, 0, 0, 2], a := ![0, 0, 0, 0, 0, 0, 0, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 1, 0, 0, 2] },
  { c := ![0, 0, 0, 0, 0, 0, 1, 1], a := ![0, 0, 0, 0, 0, 0, 1, 1],
    hac := by decide +kernel,
    verdict := .rep },
  { c := ![0, 0, 0, 0, 0, 0, 1, 1], a := ![2, 2, 2, 2, 2, 2, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 5, .g 4, .g 3, .g 1, .g 2, .g 3, .g 4, .g 5, .u, .g 5, .g 4, .g 3, .g 2, .g 1,
        .g 3, .g 4, .g 5, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 0, 0, 0, 1, 2], a := ![1, 1, 1, 1, 1, 1, 2, 0],
    hac := by decide +kernel,
    verdict := .tv
      [.g 3, .g 2, .g 3, .u]
      ![0, 0, 0, 0, 0, 0, 1, 2] ![1, 1, 1, 1, 1, 1, 1, 1] },
  { c := ![0, 0, 0, 0, 0, 0, 1, 2], a := ![2, 2, 2, 2, 2, 2, 0, 1],
    hac := by decide +kernel,
    verdict := .tv
      [.g 3, .g 2, .g 3, .u]
      ![0, 0, 0, 0, 0, 0, 2, 1] ![1, 1, 1, 1, 1, 1, 1, 1] },
  { c := ![0, 0, 0, 0, 0, 0, 2, 2], a := ![0, 0, 0, 0, 0, 0, 2, 2],
    hac := by decide +kernel,
    verdict := .conj
      [] },
  { c := ![0, 0, 0, 0, 0, 0, 2, 2], a := ![1, 1, 1, 1, 1, 1, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 5, .g 4, .g 3, .g 1, .g 2, .g 3, .g 4, .g 5, .u, .g 5, .g 4, .g 3, .g 2, .g 1,
        .g 3, .g 4, .g 5, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 0, 0, 1, 1, 2], a := ![2, 2, 2, 2, 2, 0, 0, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 3, .g 2, .g 5, .g 4, .g 3, .g 1, .u, .g 6, .g 3, .u, .g 5, .g 4, .g 3, .g 0,
        .g 2, .g 1, .g 3, .u]
      1 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 0, 0, 1, 2, 2], a := ![1, 1, 1, 1, 1, 2, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .g 3, .u, .g 3, .g 1, .g 0, .u]
      0 ![0, 0, 0, 0, 0, 1, 0, 2] },
  { c := ![0, 0, 0, 0, 1, 1, 1, 1], a := ![0, 0, 0, 0, 2, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 2, .g 3, .g 1, .g 4, .g 3, .g 2, .g 0, .u, .g 0, .g 2, .g 3, .g 4, .g 1,
        .g 3, .g 2, .g 0, .u]
      5 ![0, 0, 0, 0, 0, 1, 0, 2] },
  { c := ![0, 0, 0, 0, 1, 1, 1, 2], a := ![0, 0, 0, 0, 2, 2, 2, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 6, .g 4, .g 1, .u]
      0 ![0, 0, 0, 1, 0, 0, 0, 2] },
  { c := ![0, 0, 0, 0, 1, 1, 2, 2], a := ![1, 1, 1, 1, 0, 0, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 5, .u, .g 5, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 0, 1, 1, 2, 2], a := ![2, 2, 2, 2, 1, 1, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 5, .u, .g 5, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 0, 1, 2, 2, 2], a := ![0, 0, 0, 0, 2, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 1, .g 2, .u, .g 2, .g 1, .u]
      0 ![0, 0, 0, 0, 1, 0, 0, 2] },
  { c := ![0, 0, 0, 0, 2, 2, 2, 2], a := ![0, 0, 0, 0, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 2, .g 3, .g 1, .g 4, .g 3, .g 2, .g 0, .u, .g 0, .g 2, .g 3, .g 4, .g 1,
        .g 3, .g 2, .g 0, .u]
      5 ![0, 0, 0, 0, 0, 1, 0, 2] },
  { c := ![0, 0, 0, 1, 1, 1, 1, 1], a := ![0, 0, 0, 1, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 3, .g 4, .u, .g 4, .g 3, .g 0, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 1, 1, 1, 1], a := ![2, 2, 2, 1, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 1, 1, 1, 2], a := ![1, 1, 1, 2, 2, 2, 2, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 3, .g 2, .g 0, .g 4, .g 3, .g 1, .g 5, .g 4, .g 3, .g 2, .g 6, .g 5, .g 4, .g 3,
        .u, .g 3, .g 4, .g 5, .g 6, .g 2, .g 3, .g 4, .g 5, .g 1, .g 3, .g 4, .g 0, .g 2,
        .g 3, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 1, 1, 1, 2], a := ![2, 2, 2, 0, 0, 0, 0, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 3, .g 2, .g 0, .g 4, .g 3, .g 1, .g 5, .g 4, .g 3, .g 2, .g 6, .g 5, .g 4, .g 3,
        .u, .g 3, .g 4, .g 5, .g 6, .g 2, .g 3, .g 4, .g 5, .g 1, .g 3, .g 4, .g 0, .g 2,
        .g 3, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 1, 1, 2, 2], a := ![0, 0, 0, 1, 1, 1, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 3, .g 4, .u, .g 4, .g 3, .g 0, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 1, 1, 2, 2], a := ![1, 1, 1, 0, 0, 0, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 1, 2, 2, 2], a := ![0, 0, 0, 1, 1, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 3, .g 2, .g 4, .g 3, .g 1, .g 5, .g 4, .g 3, .u, .g 3, .g 4, .g 5, .g 1,
        .g 3, .g 4, .g 2, .g 3, .g 0, .u]
      1 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 1, 2, 2, 2], a := ![2, 2, 2, 1, 1, 0, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 3, .u, .g 3, .g 0, .u]
      1 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 2, 2, 2, 2], a := ![1, 1, 1, 2, 0, 0, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 3, .g 4, .g 6, .u, .g 6, .g 4, .g 3, .u]
      1 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 1, 2, 2, 2, 2], a := ![2, 2, 2, 0, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 3, .g 4, .g 6, .u, .g 6, .g 4, .g 3, .u]
      1 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 2, 2, 2, 2, 2], a := ![0, 0, 0, 2, 2, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 3, .g 4, .u, .g 4, .g 3, .g 0, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 0, 2, 2, 2, 2, 2], a := ![1, 1, 1, 2, 2, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 0, 1, 1, 1, 1, 1, 2], a := ![2, 2, 0, 0, 0, 0, 0, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 2, .g 3, .g 6, .g 2, .u]
      0 ![0, 0, 0, 0, 0, 1, 0, 2] },
  { c := ![0, 0, 1, 1, 1, 1, 2, 2], a := ![1, 1, 2, 2, 2, 2, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 5, .g 4, .g 3, .g 1, .g 2, .g 0, .g 3, .g 2, .g 4, .g 3, .g 5, .g 4, .g 6, .g 5,
        .u, .g 5, .g 6, .g 4, .g 5, .g 3, .g 4, .g 2, .g 3, .g 0, .g 2, .g 1, .g 3, .g 4,
        .g 5, .u]
      2 ![0, 0, 0, 0, 1, 0, 0, 2] },
  { c := ![0, 0, 1, 1, 2, 2, 2, 2], a := ![2, 2, 0, 0, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 6, .g 5, .g 4, .g 3, .g 1, .g 2, .g 3, .g 4, .g 5, .g 6, .u]
      0 ![0, 0, 0, 0, 1, 0, 0, 2] },
  { c := ![0, 0, 1, 2, 2, 2, 2, 2], a := ![1, 1, 2, 0, 0, 0, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 3, .g 4, .u, .g 4, .g 3, .g 0, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 1, 1, 1, 1, 1, 1], a := ![0, 2, 2, 2, 2, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 1, 1, 1, 1, 1, 2], a := ![0, 2, 2, 2, 2, 2, 2, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 2, .g 3, .g 1, .g 4, .g 3, .g 2, .u, .g 2, .g 3, .g 4, .g 1, .g 3, .g 2, .u]
      5 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 1, 1, 1, 1, 2, 2], a := ![1, 0, 0, 0, 0, 0, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 1, 1, 1, 1, 2, 2], a := ![2, 1, 1, 1, 1, 1, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 1, 1, 1, 2, 2, 2], a := ![0, 2, 2, 2, 2, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 1, .g 3, .g 2, .u, .g 1, .u, .g 3, .g 1, .u, .g 0, .g 2, .g 3, .g 1, .u]
      4 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 1, 1, 2, 2, 2, 2], a := ![0, 2, 2, 2, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 6, .g 4, .g 1, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 1, 2, 2, 2, 2, 2], a := ![1, 0, 0, 2, 2, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 4, .g 6, .u, .g 6, .g 4, .u]
      3 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 1, 2, 2, 2, 2, 2], a := ![2, 1, 1, 0, 0, 0, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 4, .g 6, .u, .g 6, .g 4, .u]
      3 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 1, 2, 2, 2, 2, 2, 2], a := ![0, 2, 1, 1, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![0, 2, 2, 2, 2, 2, 2, 2], a := ![0, 1, 1, 1, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![1, 1, 1, 1, 1, 1, 1, 2], a := ![0, 0, 0, 0, 0, 0, 0, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 2, .g 3, .g 5, .u, .g 5, .g 3, .g 2, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![1, 1, 1, 1, 1, 1, 1, 2], a := ![2, 2, 2, 2, 2, 2, 2, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 2, .g 3, .g 5, .u, .g 5, .g 3, .g 2, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![1, 1, 1, 1, 1, 1, 2, 2], a := ![0, 0, 0, 0, 0, 0, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 5, .g 4, .g 3, .g 1, .g 2, .g 3, .g 4, .g 5, .u, .g 5, .g 4, .g 3, .g 2, .g 1,
        .g 3, .g 4, .g 5, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![1, 1, 1, 1, 1, 1, 2, 2], a := ![1, 1, 1, 1, 1, 1, 2, 2],
    hac := by decide +kernel,
    verdict := .conj
      [.g 5, .g 4, .g 3, .g 1, .g 2, .g 0, .g 3, .g 2, .g 4, .g 3, .g 1, .g 5, .g 4, .g 3,
        .g 2, .g 0, .g 6, .g 5, .g 4, .g 3, .g 1, .g 2, .g 3, .g 4, .g 5] },
  { c := ![1, 1, 1, 1, 1, 2, 2, 2], a := ![1, 1, 1, 1, 1, 0, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 1, 0, 0, 2] },
  { c := ![1, 1, 1, 1, 1, 2, 2, 2], a := ![1, 1, 1, 1, 1, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .g 3, .u, .g 3, .g 1, .g 0, .u]
      0 ![0, 0, 0, 0, 0, 1, 0, 2] },
  { c := ![1, 1, 1, 1, 2, 2, 2, 2], a := ![0, 0, 0, 0, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .tv
      [.g 0, .g 2, .g 3, .g 4, .g 5, .g 6, .g 1, .g 3, .g 4, .g 5, .g 2, .g 3, .g 4, .g 1,
        .g 3, .g 2, .g 0, .g 2, .g 3, .g 1, .g 4, .g 3, .g 2, .g 5, .g 4, .g 3, .g 1,
        .g 6, .g 5, .g 4, .g 3, .g 2, .g 0, .u]
      ![2, 2, 2, 2, 1, 1, 1, 1] ![1, 1, 1, 1, 1, 1, 1, 1] },
  { c := ![1, 1, 1, 1, 2, 2, 2, 2], a := ![2, 2, 2, 2, 0, 0, 0, 0],
    hac := by decide +kernel,
    verdict := .tv
      [.g 0, .g 2, .g 3, .g 4, .g 5, .g 6, .g 1, .g 3, .g 4, .g 5, .g 2, .g 3, .g 4, .g 1,
        .g 3, .g 2, .g 0, .g 2, .g 3, .g 1, .g 4, .g 3, .g 2, .g 5, .g 4, .g 3, .g 1,
        .g 6, .g 5, .g 4, .g 3, .g 2, .g 0, .u]
      ![1, 1, 1, 1, 2, 2, 2, 2] ![1, 1, 1, 1, 1, 1, 1, 1] },
  { c := ![1, 1, 1, 2, 2, 2, 2, 2], a := ![0, 0, 0, 2, 2, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .u, .g 1, .g 0, .u]
      2 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![1, 1, 1, 2, 2, 2, 2, 2], a := ![1, 1, 1, 2, 2, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 3, .g 4, .u, .g 4, .g 3, .g 0, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![1, 1, 2, 2, 2, 2, 2, 2], a := ![1, 1, 0, 0, 0, 0, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 6, .g 5, .g 4, .g 3, .g 1, .g 2, .g 3, .g 4, .g 5, .g 6, .u, .g 6, .g 5, .g 4,
        .g 3, .g 2, .g 1, .g 3, .g 4, .g 5, .g 6, .u]
      0 ![0, 0, 0, 0, 0, 0, 1, 2] },
  { c := ![1, 1, 2, 2, 2, 2, 2, 2], a := ![1, 1, 2, 2, 2, 2, 2, 2],
    hac := by decide +kernel,
    verdict := .conj
      [.g 6] },
  { c := ![1, 2, 2, 2, 2, 2, 2, 2], a := ![0, 1, 1, 1, 1, 1, 1, 1],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .g 4, .g 6, .u, .g 6, .g 4, .g 1, .g 0, .u]
      0 ![0, 0, 0, 1, 0, 0, 0, 2] },
  { c := ![1, 2, 2, 2, 2, 2, 2, 2], a := ![2, 0, 0, 0, 0, 0, 0, 0],
    hac := by decide +kernel,
    verdict := .excl
      [.u, .g 0, .g 1, .g 4, .g 6, .u, .g 6, .g 4, .g 1, .g 0, .u]
      0 ![0, 0, 0, 1, 0, 0, 0, 2] }]

@[expose] def e7Pairs : List (Vn 8 × Vn 8) :=
  e7PatList.map (fun p => (p.c, p.a))

set_option maxRecDepth 20000 in
open scoped CFSG.Decide.Bounded in
theorem e7_sorted_mem : ∀ c : Vn 8, Monotone (fun i => (c i).val) → c ∈ e7Sorted := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem e7_pattern_check :
    ∀ (c : Vn 8), c ∈ e7Sorted → ∀ α : ZMod 3 → ZMod 3,
      (fun i => α (c i)) ⬝ᵥ c = 2 →
      (∀ i j, α (c i) = α (c j) ↔ c i = c j) →
      (fun i => α (c i)) ⬝ᵥ oneN 8 ≠ 0 →
      (∀ μ : ZMod 3, c ≠ μ • oneN 8) →
      (c, fun i => α (c i)) ∈ e7Pairs := by
  decide +kernel

instance (p : E7Pat) : Decidable p.check := by
  obtain ⟨pc, pa, phac, v⟩ := p
  cases v <;> simp only [E7Pat.check] <;> infer_instance

open scoped CFSG.Decide.Bounded in
theorem e7_check : ∀ p ∈ e7PatList, p.check := by
  decide +kernel


@[expose] def e7AdjWord (i : Fin 7) : List E7Gen :=
  ![[E7Gen.g 4, E7Gen.g 2, E7Gen.g 3, E7Gen.g 1, E7Gen.g 3, E7Gen.g 2, E7Gen.g 4],
    [E7Gen.g 6, E7Gen.g 5, E7Gen.g 6],
    [E7Gen.g 4, E7Gen.g 3, E7Gen.g 4],
    [E7Gen.g 2, E7Gen.g 0, E7Gen.g 2],
    [E7Gen.g 3, E7Gen.g 1, E7Gen.g 3],
    [E7Gen.g 5, E7Gen.g 4, E7Gen.g 5],
    [E7Gen.g 3, E7Gen.g 2, E7Gen.g 3]] i

theorem e7_permGroup_le :
    permGroup 8 ≤ Subgroup.closure (Set.range e7FullS) := by
  apply permGroup_le_of_adjacent (m := 7) (W := Subgroup.closure (Set.range e7FullS))
  intro i
  have h : E7Eq (E7word 1 (e7AdjWord i)) (permN (Equiv.swap i.castSucc i.succ)) := by
    fin_cases i <;> decide +kernel
  rw [← eq_of_E7Eq h]
  exact E7word_one_mem_closure _

theorem e7_stage1 {A M : Subgroup E7G}
    (hT : TestHyp (Subgroup.closure (Set.range e7FullS)) e7FullX A M)
    {u : E7G} (hu : u ∈ A) (huR : IsRefl u) (hux : ¬ FixesLine e7FullX u) :
    ∃ w ∈ Subgroup.closure (Set.range e7FullS), w * u * w⁻¹ = e7Rep := by
  obtain ⟨σ, c, f, hmono, hsym, hdot, hcne, hac, hconj⟩ :=
    TestHyp.exists_sorted e7_permGroup_le hT hu huR hux
  have hcmem : c ∈ e7Sorted := e7_sorted_mem c hmono
  have hmem : (c, fun i => f (c i)) ∈ e7Pairs :=
    e7_pattern_check c hcmem f hac hsym hdot hcne
  obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hmem
  obtain ⟨pc, pa, phac, verd⟩ := p
  have hpc : pc = c := congrArg Prod.fst hpeq
  have hpa : pa = (fun i => f (c i)) := congrArg Prod.snd hpeq
  subst pc
  subst pa
  have hchk : E7Pat.check ⟨c, (fun i => f (c i)), phac, verd⟩ :=
    e7_check ⟨c, (fun i => f (c i)), phac, verd⟩ hp
  have hconj' : permN σ * u * (permN σ)⁻¹ = refl c (fun i => f (c i)) phac := by
    rw [hconj]
    exact refl_proof_irrel _ _ _ _
  have hσA : permN σ ∈ A := hT.le (hT.W_le (e7_permGroup_le ⟨σ, rfl⟩))
  have hu0A : refl c (fun i => f (c i)) phac ∈ A := by
    rw [← hconj']
    exact A.mul_mem (A.mul_mem hσA hu) (A.inv_mem hσA)
  have hgA : ∀ k, e7FullS k ∈ A := fun k =>
    hT.le (hT.W_le (Subgroup.subset_closure ⟨k, rfl⟩))
  cases verd with
  | excl word k r =>
      obtain ⟨hr, hfix, hout⟩ := hchk
      have hmemA : E7word (refl c (fun i => f (c i)) phac) word ∈ A :=
        E7word_mem hu0A hgA word
      have hw : e7FullS k ∈ Subgroup.closure (Set.range e7FullS) :=
        Subgroup.subset_closure ⟨k, rfl⟩
      exact (hT.false_of_witness {v : Vn 8 | v ∈ e7Roots}
        (fun w hw s hs => e7_closure_maps_roots hw s hs)
        hmemA hfix hw hr hout).elim
  | tv word ct af =>
      obtain ⟨hct, haf, hdot', hbasis⟩ := hchk
      have hmemA : E7word (refl c (fun i => f (c i)) phac) word ∈ A :=
        E7word_mem hu0A hgA word
      exact (hT.noTransv _ hmemA (isTransv_of_basis hct haf hdot' hbasis)).elim
  | rep =>
      refine ⟨permN σ, e7_permGroup_le ⟨σ, rfl⟩, ?_⟩
      rw [hconj']
      simpa only [E7Pat.u] using eq_of_E7Eq hchk
  | conj word =>
      refine ⟨E7word 1 word * permN σ,
        Subgroup.mul_mem _ (E7word_one_mem_closure word)
          (e7_permGroup_le ⟨σ, rfl⟩), ?_⟩
      have hchk' :
          E7word 1 word * refl c (fun i => f (c i)) phac * (E7word 1 word)⁻¹ = e7Rep := by
        simpa only [E7Pat.u] using eq_of_E7Eq hchk
      calc (E7word 1 word * permN σ) * u * (E7word 1 word * permN σ)⁻¹
          = E7word 1 word * (permN σ * u * (permN σ)⁻¹) * (E7word 1 word)⁻¹ := by
            group
        _ = E7word 1 word * refl c (fun i => f (c i)) phac * (E7word 1 word)⁻¹ := by
            rw [hconj']
        _ = e7Rep := hchk'

theorem e7full_test (A M : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8))
    (hT : TestHyp (Subgroup.closure (Set.range e7FullS)) e7FullX A M)
    (r : Vn 8 ≃ₗ[ZMod 3] Vn 8) (hr : r ∈ M) (hrR : IsRefl r) (hrx : ¬ FixesLine e7FullX r)
    (t : Vn 8 ≃ₗ[ZMod 3] Vn 8) (ht : t ∈ A) (htR : IsRefl t) (htx : ¬ FixesLine e7FullX t) :
    t ∈ M := by
  obtain ⟨wr, hwr, hrw⟩ := e7_stage1 hT (hT.le hr) hrR hrx
  obtain ⟨wt, hwt, htw⟩ := e7_stage1 hT ht htR htx
  have hkM : wt⁻¹ * wr ∈ M :=
    M.mul_mem (M.inv_mem (hT.W_le hwt)) (hT.W_le hwr)
  have ht_eq : t = (wt⁻¹ * wr) * r * (wt⁻¹ * wr)⁻¹ := by
    calc t = wt⁻¹ * e7Rep * wt := by rw [← htw]; group
      _ = wt⁻¹ * (wr * r * wr⁻¹) * wt := by rw [← hrw]
      _ = (wt⁻¹ * wr) * r * (wt⁻¹ * wr)⁻¹ := by group
  rw [ht_eq]
  exact M.mul_mem (M.mul_mem hkM hr) (M.inv_mem hkM)

end CFSG.StandardType.TestLin

end
