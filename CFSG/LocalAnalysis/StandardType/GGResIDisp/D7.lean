module

public import CFSG.LocalAnalysis.StandardType.GGResIDispatch
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b0c5
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b0c6
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c0w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c0w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c1
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c2
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c3
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c6
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c6w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b5c6w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c0w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c0w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c1
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c2
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c3
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c5
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c5w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D7b6c5w21

public section

namespace CFSG.StandardType.GGResIDisp.D7

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
  {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V} {x : V}

@[expose] def pt_D7_b0 : Fin 7 → Fin 7 → List (Fin 7) :=
  fun j₁ j₂ => (([[[], [], [], [], [], [], []], [[], [], [2, 1], [3, 2, 1], [4, 3, 2, 1], [5, 4, 3, 2, 1], [6, 4, 3, 2, 1]], [[], [1, 2], [], [3, 2], [4, 3, 2], [5, 4, 3, 2], [6, 4, 3, 2]], [[], [1, 2, 3], [2, 3], [], [4, 3], [5, 4, 3], [6, 4, 3]], [[], [1, 2, 3, 4], [2, 3, 4], [3, 4], [], [5, 4], [6, 4]], [[], [1, 2, 3, 4, 5], [2, 3, 4, 5], [3, 4, 5], [4, 5], [], [6, 4, 5]], [[], [1, 2, 3, 4, 6], [2, 3, 4, 6], [3, 4, 6], [4, 6], [5, 4, 6], []]] : List (List (List (Fin 7)))).getD j₁ []).getD j₂ []

theorem hcyc_D7_b0 : ∀ j₁ j₂ : Fin 7, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.D 7) 0 j₁ j₂ (pt_D7_b0 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_D7_b0 : List (Fin 7 × ℤ × ℤ) := [(5, -1, -1), (6, -1, -1)]

@[expose] def vecs_D7_b0 : List (Fin 7 × ℤ × ℤ × List ℕ) :=
  [(1, -1, -2, [1, 2, 2, 2, 2, 1, 1]),
   (1, -2, -1, [2, 2, 2, 2, 2, 1, 1]),
   (1, -1, -3, [1, 2, 2, 2, 2, 1, 1]),
   (1, -3, -1, [2, 2, 2, 2, 2, 1, 1]),
   (2, -1, -1, [1, 1, 2, 2, 2, 1, 1]),
   (2, -1, -2, [1, 1, 2, 2, 2, 1, 1]),
   (2, -2, -1, [1, 1, 2, 2, 2, 1, 1]),
   (2, -1, -3, [1, 1, 2, 2, 2, 1, 1]),
   (2, -3, -1, [1, 1, 2, 2, 2, 1, 1]),
   (3, -1, -1, [2, 1, 2, 4, 4, 2, 2]),
   (3, -1, -2, [1, 1, 2, 3, 2, 1, 1]),
   (3, -2, -1, [2, 1, 2, 3, 2, 1, 1]),
   (3, -1, -3, [1, 1, 2, 3, 2, 1, 1]),
   (3, -3, -1, [2, 1, 2, 3, 2, 1, 1]),
   (4, -1, -1, [2, 1, 2, 3, 4, 2, 1]),
   (4, -1, -2, [2, 1, 2, 3, 4, 1, 1]),
   (4, -2, -1, [3, 1, 2, 3, 4, 1, 1]),
   (4, -1, -3, [1, 1, 2, 3, 4, 1, 1]),
   (4, -3, -1, [3, 1, 2, 3, 4, 1, 1]),
   (5, -1, -2, [1, 1, 2, 3, 4, 3, 2]),
   (5, -2, -1, [2, 1, 2, 3, 4, 3, 2]),
   (5, -1, -3, [1, 1, 2, 3, 4, 3, 2]),
   (5, -3, -1, [2, 1, 2, 3, 4, 3, 2]),
   (6, -1, -2, [1, 1, 2, 3, 4, 2, 3]),
   (6, -2, -1, [2, 1, 2, 3, 4, 2, 3]),
   (6, -1, -3, [1, 1, 2, 3, 4, 2, 3]),
   (6, -3, -1, [2, 1, 2, 3, 4, 2, 3])]

theorem hcand_D7_b0 : ∀ ic : Fin 7, ic ≠ 0 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.D 7) 0 ic pr.1 pr.2 shapes_D7_b0 vecs_D7_b0 = true := by
  decide +kernel

theorem hshapes_D7_b0 : ∀ s ∈ shapes_D7_b0, GGResIShapeOK (CartanMatrix.D 7) 0 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_D7_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact GGResIShape.D7b0c5.ok
  · exact GGResIShape.D7b0c6.ok

theorem case_D7_b0 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 7 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) (hib : e 0 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 1 (by decide) pt_D7_b0 hcyc_D7_b0 shapes_D7_b0 vecs_D7_b0 hcand_D7_b0
    hshapes_D7_b0

theorem case_D7_b1 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) (hib : e 1 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0} 0 2 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_D7_b2 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) (hib : e 2 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1} 1 3 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_D7_b3 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) (hib : e 3 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1, 2} 2 4 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_D7_b4 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) (hib : e 4 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1, 2, 3} 3 5 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

@[expose] def pt_D7_b5 : Fin 7 → Fin 7 → List (Fin 7) :=
  fun j₁ j₂ => (([[[], [1, 0], [2, 1, 0], [3, 2, 1, 0], [4, 3, 2, 1, 0], [], [6, 4, 3, 2, 1, 0]], [[0, 1], [], [2, 1], [3, 2, 1], [4, 3, 2, 1], [], [6, 4, 3, 2, 1]], [[0, 1, 2], [1, 2], [], [3, 2], [4, 3, 2], [], [6, 4, 3, 2]], [[0, 1, 2, 3], [1, 2, 3], [2, 3], [], [4, 3], [], [6, 4, 3]], [[0, 1, 2, 3, 4], [1, 2, 3, 4], [2, 3, 4], [3, 4], [], [], [6, 4]], [[], [], [], [], [], [], []], [[0, 1, 2, 3, 4, 6], [1, 2, 3, 4, 6], [2, 3, 4, 6], [3, 4, 6], [4, 6], [], []]] : List (List (List (Fin 7)))).getD j₁ []).getD j₂ []

theorem hcyc_D7_b5 : ∀ j₁ j₂ : Fin 7, j₁ ≠ 5 → j₂ ≠ 5 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.D 7) 5 j₁ j₂ (pt_D7_b5 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_D7_b5 : List (Fin 7 × ℤ × ℤ) := [(0, -1, -1), (0, -1, -2), (0, -2, -1), (1, -1, -1), (2, -1, -1), (3, -1, -1), (6, -1, -1), (6, -1, -2), (6, -2, -1)]

@[expose] def vecs_D7_b5 : List (Fin 7 × ℤ × ℤ × List ℕ) :=
  [(0, -1, -3, [6, 5, 4, 3, 2, 3, 1]),
   (0, -3, -1, [6, 5, 4, 3, 2, 7, 1]),
   (1, -1, -2, [2, 5, 4, 3, 2, 2, 1]),
   (1, -2, -1, [2, 5, 4, 3, 2, 4, 1]),
   (1, -1, -3, [1, 5, 4, 3, 2, 2, 1]),
   (1, -3, -1, [2, 5, 4, 3, 2, 4, 1]),
   (2, -1, -2, [1, 2, 4, 3, 2, 2, 1]),
   (2, -2, -1, [1, 2, 4, 3, 2, 3, 1]),
   (2, -1, -3, [1, 2, 4, 3, 2, 1, 1]),
   (2, -3, -1, [1, 2, 4, 3, 2, 3, 1]),
   (3, -1, -2, [1, 2, 3, 4, 2, 2, 1]),
   (3, -2, -1, [1, 2, 3, 4, 2, 3, 1]),
   (3, -1, -3, [1, 2, 3, 4, 2, 1, 1]),
   (3, -3, -1, [1, 2, 3, 4, 2, 3, 1]),
   (4, -1, -2, [1, 2, 3, 4, 5, 2, 2]),
   (4, -2, -1, [1, 2, 3, 4, 5, 5, 1]),
   (4, -1, -3, [1, 2, 3, 4, 5, 2, 1]),
   (4, -3, -1, [1, 2, 3, 4, 5, 5, 1]),
   (6, -1, -3, [1, 2, 3, 4, 5, 3, 6]),
   (6, -3, -1, [1, 2, 3, 4, 5, 7, 6])]

theorem hcand_D7_b5 : ∀ ic : Fin 7, ic ≠ 5 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.D 7) 5 ic pr.1 pr.2 shapes_D7_b5 vecs_D7_b5 = true := by
  decide +kernel

theorem hshapes_D7_b5 : ∀ s ∈ shapes_D7_b5, GGResIShapeOK (CartanMatrix.D 7) 5 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_D7_b5, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.D7b5c0.ok
  · exact GGResIShape.D7b5c0w12.ok
  · exact GGResIShape.D7b5c0w21.ok
  · exact GGResIShape.D7b5c1.ok
  · exact GGResIShape.D7b5c2.ok
  · exact GGResIShape.D7b5c3.ok
  · exact GGResIShape.D7b5c6.ok
  · exact GGResIShape.D7b5c6w12.ok
  · exact GGResIShape.D7b5c6w21.ok

theorem case_D7_b5 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 7 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) (hib : e 5 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_D7_b5 hcyc_D7_b5 shapes_D7_b5 vecs_D7_b5 hcand_D7_b5
    hshapes_D7_b5

@[expose] def pt_D7_b6 : Fin 7 → Fin 7 → List (Fin 7) :=
  fun j₁ j₂ => (([[[], [1, 0], [2, 1, 0], [3, 2, 1, 0], [4, 3, 2, 1, 0], [5, 4, 3, 2, 1, 0], []], [[0, 1], [], [2, 1], [3, 2, 1], [4, 3, 2, 1], [5, 4, 3, 2, 1], []], [[0, 1, 2], [1, 2], [], [3, 2], [4, 3, 2], [5, 4, 3, 2], []], [[0, 1, 2, 3], [1, 2, 3], [2, 3], [], [4, 3], [5, 4, 3], []], [[0, 1, 2, 3, 4], [1, 2, 3, 4], [2, 3, 4], [3, 4], [], [5, 4], []], [[0, 1, 2, 3, 4, 5], [1, 2, 3, 4, 5], [2, 3, 4, 5], [3, 4, 5], [4, 5], [], []], [[], [], [], [], [], [], []]] : List (List (List (Fin 7)))).getD j₁ []).getD j₂ []

theorem hcyc_D7_b6 : ∀ j₁ j₂ : Fin 7, j₁ ≠ 6 → j₂ ≠ 6 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.D 7) 6 j₁ j₂ (pt_D7_b6 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_D7_b6 : List (Fin 7 × ℤ × ℤ) := [(0, -1, -1), (0, -1, -2), (0, -2, -1), (1, -1, -1), (2, -1, -1), (3, -1, -1), (5, -1, -1), (5, -1, -2), (5, -2, -1)]

@[expose] def vecs_D7_b6 : List (Fin 7 × ℤ × ℤ × List ℕ) :=
  [(0, -1, -3, [6, 5, 4, 3, 2, 1, 3]),
   (0, -3, -1, [6, 5, 4, 3, 2, 1, 7]),
   (1, -1, -2, [2, 5, 4, 3, 2, 1, 2]),
   (1, -2, -1, [2, 5, 4, 3, 2, 1, 4]),
   (1, -1, -3, [1, 5, 4, 3, 2, 1, 2]),
   (1, -3, -1, [2, 5, 4, 3, 2, 1, 4]),
   (2, -1, -2, [1, 2, 4, 3, 2, 1, 2]),
   (2, -2, -1, [1, 2, 4, 3, 2, 1, 3]),
   (2, -1, -3, [1, 2, 4, 3, 2, 1, 1]),
   (2, -3, -1, [1, 2, 4, 3, 2, 1, 3]),
   (3, -1, -2, [1, 2, 3, 4, 2, 1, 2]),
   (3, -2, -1, [1, 2, 3, 4, 2, 1, 3]),
   (3, -1, -3, [1, 2, 3, 4, 2, 1, 1]),
   (3, -3, -1, [1, 2, 3, 4, 2, 1, 3]),
   (4, -1, -2, [1, 2, 3, 4, 5, 2, 2]),
   (4, -2, -1, [1, 2, 3, 4, 5, 2, 4]),
   (4, -1, -3, [1, 2, 3, 4, 5, 1, 2]),
   (4, -3, -1, [1, 2, 3, 4, 5, 2, 4]),
   (5, -1, -3, [1, 2, 3, 4, 5, 6, 3]),
   (5, -3, -1, [1, 2, 3, 4, 5, 6, 7])]

theorem hcand_D7_b6 : ∀ ic : Fin 7, ic ≠ 6 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.D 7) 6 ic pr.1 pr.2 shapes_D7_b6 vecs_D7_b6 = true := by
  decide +kernel

theorem hshapes_D7_b6 : ∀ s ∈ shapes_D7_b6, GGResIShapeOK (CartanMatrix.D 7) 6 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_D7_b6, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.D7b6c0.ok
  · exact GGResIShape.D7b6c0w12.ok
  · exact GGResIShape.D7b6c0w21.ok
  · exact GGResIShape.D7b6c1.ok
  · exact GGResIShape.D7b6c2.ok
  · exact GGResIShape.D7b6c3.ok
  · exact GGResIShape.D7b6c5.ok
  · exact GGResIShape.D7b6c5w12.ok
  · exact GGResIShape.D7b6c5w21.ok

theorem case_D7_b6 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 7 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) (hib : e 6 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_D7_b6 hcyc_D7_b6 shapes_D7_b6 vecs_D7_b6 hcand_D7_b6
    hshapes_D7_b6

theorem ggResI_type_D7 [Module.Finite (ZMod p) V] [Finite V]
    (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 7 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) : GGResILinConcl p b CL CK g h α x := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact case_D7_b0 H e hCe hk
  · exact case_D7_b1 H e hCe hk
  · exact case_D7_b2 H e hCe hk
  · exact case_D7_b3 H e hCe hk
  · exact case_D7_b4 H e hCe hk
  · exact case_D7_b5 H e hCe hk
  · exact case_D7_b6 H e hCe hk

end CFSG.StandardType.GGResIDisp.D7
