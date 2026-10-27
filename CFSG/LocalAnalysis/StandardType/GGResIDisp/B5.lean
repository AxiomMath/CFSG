module

public import CFSG.LocalAnalysis.StandardType.GGResIDispatch
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B5b4c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B5b4c0w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B5b4c0w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B5b4c1
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B5b4c2
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B5b4c3
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B5b4c3w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B5b4c3w21

public section

namespace CFSG.StandardType.GGResIDisp.B5

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
  {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V} {x : V}

@[expose] def pt_B5_b0 : Fin 5 → Fin 5 → List (Fin 5) :=
  fun j₁ j₂ => (([[[], [], [], [], []], [[], [], [2, 1], [3, 2, 1], [4, 3, 2, 1]], [[], [1, 2], [], [3, 2], [4, 3, 2]], [[], [1, 2, 3], [2, 3], [], [4, 3]], [[], [1, 2, 3, 4], [2, 3, 4], [3, 4], []]] : List (List (List (Fin 5)))).getD j₁ []).getD j₂ []

theorem hcyc_B5_b0 : ∀ j₁ j₂ : Fin 5, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.B 5) 0 j₁ j₂ (pt_B5_b0 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_B5_b0 : List (Fin 5 × ℤ × ℤ) := []

@[expose] def vecs_B5_b0 : List (Fin 5 × ℤ × ℤ × List ℕ) :=
  [(1, -1, -2, [1, 2, 2, 2, 1]),
   (1, -2, -1, [2, 2, 2, 2, 1]),
   (1, -1, -3, [1, 2, 2, 2, 1]),
   (1, -3, -1, [2, 2, 2, 2, 1]),
   (2, -1, -1, [1, 1, 2, 2, 1]),
   (2, -1, -2, [1, 1, 2, 2, 1]),
   (2, -2, -1, [1, 1, 2, 2, 1]),
   (2, -1, -3, [1, 1, 2, 2, 1]),
   (2, -3, -1, [1, 1, 2, 2, 1]),
   (3, -1, -1, [2, 1, 2, 4, 2]),
   (3, -1, -2, [1, 1, 2, 3, 1]),
   (3, -2, -1, [2, 1, 2, 3, 1]),
   (3, -1, -3, [1, 1, 2, 3, 1]),
   (3, -3, -1, [2, 1, 2, 3, 1]),
   (4, -1, -1, [1, 1, 2, 3, 2]),
   (4, -1, -2, [1, 1, 2, 3, 2]),
   (4, -2, -1, [1, 1, 2, 3, 2]),
   (4, -1, -3, [1, 1, 2, 3, 2]),
   (4, -3, -1, [1, 1, 2, 3, 2])]

theorem hcand_B5_b0 : ∀ ic : Fin 5, ic ≠ 0 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.B 5) 0 ic pr.1 pr.2 shapes_B5_b0 vecs_B5_b0 = true := by
  decide +kernel

theorem hshapes_B5_b0 : ∀ s ∈ shapes_B5_b0, GGResIShapeOK (CartanMatrix.B 5) 0 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp [shapes_B5_b0] at hs

theorem case_B5_b0 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 5 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 5) i j) (hib : e 0 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 1 (by decide) pt_B5_b0 hcyc_B5_b0 shapes_B5_b0 vecs_B5_b0 hcand_B5_b0
    hshapes_B5_b0

theorem case_B5_b1 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 5) i j) (hib : e 1 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0} 0 2 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_B5_b2 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 5) i j) (hib : e 2 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1} 1 3 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_B5_b3 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 5) i j) (hib : e 3 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1, 2} 2 4 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

@[expose] def pt_B5_b4 : Fin 5 → Fin 5 → List (Fin 5) :=
  fun j₁ j₂ => (([[[], [1, 0], [2, 1, 0], [3, 2, 1, 0], []], [[0, 1], [], [2, 1], [3, 2, 1], []], [[0, 1, 2], [1, 2], [], [3, 2], []], [[0, 1, 2, 3], [1, 2, 3], [2, 3], [], []], [[], [], [], [], []]] : List (List (List (Fin 5)))).getD j₁ []).getD j₂ []

theorem hcyc_B5_b4 : ∀ j₁ j₂ : Fin 5, j₁ ≠ 4 → j₂ ≠ 4 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.B 5) 4 j₁ j₂ (pt_B5_b4 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_B5_b4 : List (Fin 5 × ℤ × ℤ) := [(0, -1, -1), (0, -1, -2), (0, -2, -1), (1, -1, -1), (2, -1, -1), (3, -1, -1), (3, -1, -2), (3, -2, -1)]

@[expose] def vecs_B5_b4 : List (Fin 5 × ℤ × ℤ × List ℕ) :=
  [(0, -1, -3, [4, 3, 2, 1, 2]),
   (0, -3, -1, [4, 3, 2, 1, 5]),
   (1, -1, -2, [2, 4, 2, 1, 2]),
   (1, -2, -1, [1, 3, 2, 1, 3]),
   (1, -1, -3, [1, 3, 2, 1, 1]),
   (1, -3, -1, [1, 3, 2, 1, 3]),
   (2, -1, -2, [1, 2, 4, 2, 2]),
   (2, -2, -1, [1, 2, 3, 1, 3]),
   (2, -1, -3, [1, 2, 3, 1, 1]),
   (2, -3, -1, [1, 2, 3, 1, 3]),
   (3, -1, -3, [1, 2, 3, 4, 2]),
   (3, -3, -1, [1, 2, 3, 4, 5])]

theorem hcand_B5_b4 : ∀ ic : Fin 5, ic ≠ 4 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.B 5) 4 ic pr.1 pr.2 shapes_B5_b4 vecs_B5_b4 = true := by
  decide +kernel

theorem hshapes_B5_b4 : ∀ s ∈ shapes_B5_b4, GGResIShapeOK (CartanMatrix.B 5) 4 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_B5_b4, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.B5b4c0.ok
  · exact GGResIShape.B5b4c0w12.ok
  · exact GGResIShape.B5b4c0w21.ok
  · exact GGResIShape.B5b4c1.ok
  · exact GGResIShape.B5b4c2.ok
  · exact GGResIShape.B5b4c3.ok
  · exact GGResIShape.B5b4c3w12.ok
  · exact GGResIShape.B5b4c3w21.ok

theorem case_B5_b4 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 5 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 5) i j) (hib : e 4 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_B5_b4 hcyc_B5_b4 shapes_B5_b4 vecs_B5_b4 hcand_B5_b4
    hshapes_B5_b4

theorem ggResI_type_B5 [Module.Finite (ZMod p) V] [Finite V]
    (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 5 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 5) i j) : GGResILinConcl p b CL CK g h α x := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact case_B5_b0 H e hCe hk
  · exact case_B5_b1 H e hCe hk
  · exact case_B5_b2 H e hCe hk
  · exact case_B5_b3 H e hCe hk
  · exact case_B5_b4 H e hCe hk

end CFSG.StandardType.GGResIDisp.B5
