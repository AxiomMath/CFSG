module

public import CFSG.LocalAnalysis.StandardType.GGResIDispatch
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b0c5
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b1c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b1c0w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b1c0w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b1c2
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b1c4
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b1c5
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b1c5w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b1c5w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b5c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.E6b5c1

public section

namespace CFSG.StandardType.GGResIDisp.E6

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
  {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V} {x : V}

@[expose] def pt_E6_b0 : Fin 6 → Fin 6 → List (Fin 6) :=
  fun j₁ j₂ => (([[[], [], [], [], [], []], [[], [], [2, 3, 1], [3, 1], [4, 3, 1], [5, 4, 3, 1]], [[], [1, 3, 2], [], [3, 2], [4, 3, 2], [5, 4, 3, 2]], [[], [1, 3], [2, 3], [], [4, 3], [5, 4, 3]], [[], [1, 3, 4], [2, 3, 4], [3, 4], [], [5, 4]], [[], [1, 3, 4, 5], [2, 3, 4, 5], [3, 4, 5], [4, 5], []]] : List (List (List (Fin 6)))).getD j₁ []).getD j₂ []

theorem hcyc_E6_b0 : ∀ j₁ j₂ : Fin 6, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.E 6) 0 j₁ j₂ (pt_E6_b0 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_E6_b0 : List (Fin 6 × ℤ × ℤ) := [(1, -1, -1), (5, -1, -1)]

@[expose] def vecs_E6_b0 : List (Fin 6 × ℤ × ℤ × List ℕ) :=
  [(1, -1, -2, [2, 4, 2, 4, 2, 1]),
   (1, -2, -1, [3, 3, 1, 3, 2, 1]),
   (1, -1, -3, [1, 3, 1, 3, 2, 1]),
   (1, -3, -1, [3, 3, 1, 3, 2, 1]),
   (2, -1, -2, [2, 2, 4, 4, 2, 1]),
   (2, -2, -1, [3, 1, 3, 3, 2, 1]),
   (2, -1, -3, [1, 1, 3, 3, 2, 1]),
   (2, -3, -1, [3, 1, 3, 3, 2, 1]),
   (3, -1, -1, [2, 2, 2, 4, 2, 1]),
   (3, -1, -2, [1, 1, 1, 3, 2, 1]),
   (3, -2, -1, [2, 1, 1, 3, 2, 1]),
   (3, -1, -3, [1, 1, 1, 3, 2, 1]),
   (3, -3, -1, [2, 1, 1, 3, 2, 1]),
   (4, -1, -1, [1, 1, 1, 2, 2, 1]),
   (4, -1, -2, [1, 1, 1, 2, 2, 1]),
   (4, -2, -1, [1, 1, 1, 2, 2, 1]),
   (4, -1, -3, [1, 1, 1, 2, 2, 1]),
   (4, -3, -1, [1, 1, 1, 2, 2, 1]),
   (5, -1, -2, [1, 1, 1, 2, 2, 2]),
   (5, -2, -1, [2, 1, 1, 2, 2, 2]),
   (5, -1, -3, [1, 1, 1, 2, 2, 2]),
   (5, -3, -1, [2, 1, 1, 2, 2, 2])]

theorem hcand_E6_b0 : ∀ ic : Fin 6, ic ≠ 0 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.E 6) 0 ic pr.1 pr.2 shapes_E6_b0 vecs_E6_b0 = true := by
  decide +kernel

theorem hshapes_E6_b0 : ∀ s ∈ shapes_E6_b0, GGResIShapeOK (CartanMatrix.E 6) 0 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_E6_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact GGResIShape.E6b0c1.ok
  · exact GGResIShape.E6b0c5.ok

theorem case_E6_b0 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 6 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.E 6) i j) (hib : e 0 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 1 (by decide) pt_E6_b0 hcyc_E6_b0 shapes_E6_b0 vecs_E6_b0 hcand_E6_b0
    hshapes_E6_b0

@[expose] def pt_E6_b1 : Fin 6 → Fin 6 → List (Fin 6) :=
  fun j₁ j₂ => (([[[], [], [2, 0], [3, 2, 0], [4, 3, 2, 0], [5, 4, 3, 2, 0]], [[], [], [], [], [], []], [[0, 2], [], [], [3, 2], [4, 3, 2], [5, 4, 3, 2]], [[0, 2, 3], [], [2, 3], [], [4, 3], [5, 4, 3]], [[0, 2, 3, 4], [], [2, 3, 4], [3, 4], [], [5, 4]], [[0, 2, 3, 4, 5], [], [2, 3, 4, 5], [3, 4, 5], [4, 5], []]] : List (List (List (Fin 6)))).getD j₁ []).getD j₂ []

theorem hcyc_E6_b1 : ∀ j₁ j₂ : Fin 6, j₁ ≠ 1 → j₂ ≠ 1 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.E 6) 1 j₁ j₂ (pt_E6_b1 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_E6_b1 : List (Fin 6 × ℤ × ℤ) := [(0, -1, -1), (0, -1, -2), (0, -2, -1), (2, -1, -1), (4, -1, -1), (5, -1, -1), (5, -1, -2), (5, -2, -1)]

@[expose] def vecs_E6_b1 : List (Fin 6 × ℤ × ℤ × List ℕ) :=
  [(0, -1, -3, [5, 2, 4, 3, 2, 1]),
   (0, -3, -1, [5, 6, 4, 3, 2, 1]),
   (2, -1, -2, [1, 2, 4, 3, 2, 1]),
   (2, -2, -1, [2, 3, 4, 3, 2, 1]),
   (2, -1, -3, [1, 2, 4, 3, 2, 1]),
   (2, -3, -1, [2, 3, 4, 3, 2, 1]),
   (3, -1, -2, [1, 1, 2, 3, 2, 1]),
   (3, -2, -1, [1, 2, 2, 3, 2, 1]),
   (3, -1, -3, [1, 1, 2, 3, 2, 1]),
   (3, -3, -1, [1, 2, 2, 3, 2, 1]),
   (4, -1, -2, [1, 2, 2, 3, 4, 1]),
   (4, -2, -1, [1, 4, 2, 3, 4, 1]),
   (4, -1, -3, [1, 2, 2, 3, 4, 1]),
   (4, -3, -1, [1, 4, 2, 3, 4, 1]),
   (5, -1, -3, [1, 2, 2, 3, 4, 5]),
   (5, -3, -1, [1, 6, 2, 3, 4, 5])]

theorem hcand_E6_b1 : ∀ ic : Fin 6, ic ≠ 1 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.E 6) 1 ic pr.1 pr.2 shapes_E6_b1 vecs_E6_b1 = true := by
  decide +kernel

theorem hshapes_E6_b1 : ∀ s ∈ shapes_E6_b1, GGResIShapeOK (CartanMatrix.E 6) 1 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_E6_b1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.E6b1c0.ok
  · exact GGResIShape.E6b1c0w12.ok
  · exact GGResIShape.E6b1c0w21.ok
  · exact GGResIShape.E6b1c2.ok
  · exact GGResIShape.E6b1c4.ok
  · exact GGResIShape.E6b1c5.ok
  · exact GGResIShape.E6b1c5w12.ok
  · exact GGResIShape.E6b1c5w21.ok

theorem case_E6_b1 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 6 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.E 6) i j) (hib : e 1 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_E6_b1 hcyc_E6_b1 shapes_E6_b1 vecs_E6_b1 hcand_E6_b1
    hshapes_E6_b1

theorem case_E6_b2 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.E 6) i j) (hib : e 2 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0} 0 3 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_E6_b3 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.E 6) i j) (hib : e 3 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {1} 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_E6_b4 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.E 6) i j) (hib : e 4 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1, 2, 3} 3 5 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

@[expose] def pt_E6_b5 : Fin 6 → Fin 6 → List (Fin 6) :=
  fun j₁ j₂ => (([[[], [1, 3, 2, 0], [2, 0], [3, 2, 0], [4, 3, 2, 0], []], [[0, 2, 3, 1], [], [2, 3, 1], [3, 1], [4, 3, 1], []], [[0, 2], [1, 3, 2], [], [3, 2], [4, 3, 2], []], [[0, 2, 3], [1, 3], [2, 3], [], [4, 3], []], [[0, 2, 3, 4], [1, 3, 4], [2, 3, 4], [3, 4], [], []], [[], [], [], [], [], []]] : List (List (List (Fin 6)))).getD j₁ []).getD j₂ []

theorem hcyc_E6_b5 : ∀ j₁ j₂ : Fin 6, j₁ ≠ 5 → j₂ ≠ 5 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.E 6) 5 j₁ j₂ (pt_E6_b5 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_E6_b5 : List (Fin 6 × ℤ × ℤ) := [(0, -1, -1), (1, -1, -1)]

@[expose] def vecs_E6_b5 : List (Fin 6 × ℤ × ℤ × List ℕ) :=
  [(0, -1, -2, [2, 1, 2, 2, 1, 1]),
   (0, -2, -1, [2, 1, 2, 2, 1, 2]),
   (0, -1, -3, [2, 1, 2, 2, 1, 1]),
   (0, -3, -1, [2, 1, 2, 2, 1, 2]),
   (1, -1, -2, [1, 4, 2, 4, 2, 2]),
   (1, -2, -1, [1, 3, 2, 3, 1, 3]),
   (1, -1, -3, [1, 3, 2, 3, 1, 1]),
   (1, -3, -1, [1, 3, 2, 3, 1, 3]),
   (2, -1, -1, [1, 1, 2, 2, 1, 1]),
   (2, -1, -2, [1, 1, 2, 2, 1, 1]),
   (2, -2, -1, [1, 1, 2, 2, 1, 1]),
   (2, -1, -3, [1, 1, 2, 2, 1, 1]),
   (2, -3, -1, [1, 1, 2, 2, 1, 1]),
   (3, -1, -1, [1, 2, 2, 4, 2, 2]),
   (3, -1, -2, [1, 1, 2, 3, 1, 1]),
   (3, -2, -1, [1, 1, 2, 3, 1, 2]),
   (3, -1, -3, [1, 1, 2, 3, 1, 1]),
   (3, -3, -1, [1, 1, 2, 3, 1, 2]),
   (4, -1, -2, [1, 2, 2, 4, 4, 2]),
   (4, -2, -1, [1, 1, 2, 3, 3, 3]),
   (4, -1, -3, [1, 1, 2, 3, 3, 1]),
   (4, -3, -1, [1, 1, 2, 3, 3, 3])]

theorem hcand_E6_b5 : ∀ ic : Fin 6, ic ≠ 5 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.E 6) 5 ic pr.1 pr.2 shapes_E6_b5 vecs_E6_b5 = true := by
  decide +kernel

theorem hshapes_E6_b5 : ∀ s ∈ shapes_E6_b5, GGResIShapeOK (CartanMatrix.E 6) 5 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_E6_b5, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact GGResIShape.E6b5c0.ok
  · exact GGResIShape.E6b5c1.ok

theorem case_E6_b5 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 6 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.E 6) i j) (hib : e 5 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_E6_b5 hcyc_E6_b5 shapes_E6_b5 vecs_E6_b5 hcand_E6_b5
    hshapes_E6_b5

theorem ggResI_type_E6 [Module.Finite (ZMod p) V] [Finite V]
    (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 6 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.E 6) i j) : GGResILinConcl p b CL CK g h α x := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact case_E6_b0 H e hCe hk
  · exact case_E6_b1 H e hCe hk
  · exact case_E6_b2 H e hCe hk
  · exact case_E6_b3 H e hCe hk
  · exact case_E6_b4 H e hCe hk
  · exact case_E6_b5 H e hCe hk

end CFSG.StandardType.GGResIDisp.E6
