module

public import CFSG.LocalAnalysis.StandardType.GGResIDispatch
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b0c2
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b0c2w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b0c2w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b0c3
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b0c3w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b0c3w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b2c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b2c0w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b2c0w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b2c3
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b2c3w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b2c3w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b3c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b3c0w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b3c0w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b3c2
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b3c2w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.D4b3c2w21

public section

namespace CFSG.StandardType.GGResIDisp.D4

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
  {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V} {x : V}

@[expose] def pt_D4_b0 : Fin 4 → Fin 4 → List (Fin 4) :=
  fun j₁ j₂ => (([[[], [], [], []], [[], [], [2, 1], [3, 1]], [[], [1, 2], [], [3, 1, 2]], [[], [1, 3], [2, 1, 3], []]] : List (List (List (Fin 4)))).getD j₁ []).getD j₂ []

theorem hcyc_D4_b0 : ∀ j₁ j₂ : Fin 4, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.D 4) 0 j₁ j₂ (pt_D4_b0 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_D4_b0 : List (Fin 4 × ℤ × ℤ) := [(2, -1, -1), (2, -1, -2), (2, -2, -1), (3, -1, -1), (3, -1, -2), (3, -2, -1)]

@[expose] def vecs_D4_b0 : List (Fin 4 × ℤ × ℤ × List ℕ) :=
  [(1, -1, -2, [1, 2, 1, 1]),
   (1, -2, -1, [2, 2, 1, 1]),
   (1, -1, -3, [1, 2, 1, 1]),
   (1, -3, -1, [2, 2, 1, 1]),
   (2, -1, -3, [2, 2, 4, 1]),
   (2, -3, -1, [4, 2, 3, 1]),
   (3, -1, -3, [2, 2, 1, 4]),
   (3, -3, -1, [4, 2, 1, 3])]

theorem hcand_D4_b0 : ∀ ic : Fin 4, ic ≠ 0 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.D 4) 0 ic pr.1 pr.2 shapes_D4_b0 vecs_D4_b0 = true := by
  decide +kernel

theorem hshapes_D4_b0 : ∀ s ∈ shapes_D4_b0, GGResIShapeOK (CartanMatrix.D 4) 0 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_D4_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.D4b0c2.ok
  · exact GGResIShape.D4b0c2w12.ok
  · exact GGResIShape.D4b0c2w21.ok
  · exact GGResIShape.D4b0c3.ok
  · exact GGResIShape.D4b0c3w12.ok
  · exact GGResIShape.D4b0c3w21.ok

theorem case_D4_b0 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 4 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 4) i j) (hib : e 0 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 1 (by decide) pt_D4_b0 hcyc_D4_b0 shapes_D4_b0 vecs_D4_b0 hcand_D4_b0
    hshapes_D4_b0

theorem case_D4_b1 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 4 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 4) i j) (hib : e 1 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0} 0 2 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

@[expose] def pt_D4_b2 : Fin 4 → Fin 4 → List (Fin 4) :=
  fun j₁ j₂ => (([[[], [1, 0], [], [3, 1, 0]], [[0, 1], [], [], [3, 1]], [[], [], [], []], [[0, 1, 3], [1, 3], [], []]] : List (List (List (Fin 4)))).getD j₁ []).getD j₂ []

theorem hcyc_D4_b2 : ∀ j₁ j₂ : Fin 4, j₁ ≠ 2 → j₂ ≠ 2 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.D 4) 2 j₁ j₂ (pt_D4_b2 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_D4_b2 : List (Fin 4 × ℤ × ℤ) := [(0, -1, -1), (0, -1, -2), (0, -2, -1), (3, -1, -1), (3, -1, -2), (3, -2, -1)]

@[expose] def vecs_D4_b2 : List (Fin 4 × ℤ × ℤ × List ℕ) :=
  [(0, -1, -3, [4, 2, 2, 1]),
   (0, -3, -1, [3, 2, 4, 1]),
   (1, -1, -2, [1, 2, 1, 1]),
   (1, -2, -1, [1, 2, 2, 1]),
   (1, -1, -3, [1, 2, 1, 1]),
   (1, -3, -1, [1, 2, 2, 1]),
   (3, -1, -3, [1, 2, 2, 4]),
   (3, -3, -1, [1, 2, 4, 3])]

theorem hcand_D4_b2 : ∀ ic : Fin 4, ic ≠ 2 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.D 4) 2 ic pr.1 pr.2 shapes_D4_b2 vecs_D4_b2 = true := by
  decide +kernel

theorem hshapes_D4_b2 : ∀ s ∈ shapes_D4_b2, GGResIShapeOK (CartanMatrix.D 4) 2 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_D4_b2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.D4b2c0.ok
  · exact GGResIShape.D4b2c0w12.ok
  · exact GGResIShape.D4b2c0w21.ok
  · exact GGResIShape.D4b2c3.ok
  · exact GGResIShape.D4b2c3w12.ok
  · exact GGResIShape.D4b2c3w21.ok

theorem case_D4_b2 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 4 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 4) i j) (hib : e 2 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_D4_b2 hcyc_D4_b2 shapes_D4_b2 vecs_D4_b2 hcand_D4_b2
    hshapes_D4_b2

@[expose] def pt_D4_b3 : Fin 4 → Fin 4 → List (Fin 4) :=
  fun j₁ j₂ => (([[[], [1, 0], [2, 1, 0], []], [[0, 1], [], [2, 1], []], [[0, 1, 2], [1, 2], [], []], [[], [], [], []]] : List (List (List (Fin 4)))).getD j₁ []).getD j₂ []

theorem hcyc_D4_b3 : ∀ j₁ j₂ : Fin 4, j₁ ≠ 3 → j₂ ≠ 3 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.D 4) 3 j₁ j₂ (pt_D4_b3 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_D4_b3 : List (Fin 4 × ℤ × ℤ) := [(0, -1, -1), (0, -1, -2), (0, -2, -1), (2, -1, -1), (2, -1, -2), (2, -2, -1)]

@[expose] def vecs_D4_b3 : List (Fin 4 × ℤ × ℤ × List ℕ) :=
  [(0, -1, -3, [4, 2, 1, 2]),
   (0, -3, -1, [3, 2, 1, 4]),
   (1, -1, -2, [1, 2, 1, 1]),
   (1, -2, -1, [1, 2, 1, 2]),
   (1, -1, -3, [1, 2, 1, 1]),
   (1, -3, -1, [1, 2, 1, 2]),
   (2, -1, -3, [1, 2, 4, 2]),
   (2, -3, -1, [1, 2, 3, 4])]

theorem hcand_D4_b3 : ∀ ic : Fin 4, ic ≠ 3 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.D 4) 3 ic pr.1 pr.2 shapes_D4_b3 vecs_D4_b3 = true := by
  decide +kernel

theorem hshapes_D4_b3 : ∀ s ∈ shapes_D4_b3, GGResIShapeOK (CartanMatrix.D 4) 3 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_D4_b3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.D4b3c0.ok
  · exact GGResIShape.D4b3c0w12.ok
  · exact GGResIShape.D4b3c0w21.ok
  · exact GGResIShape.D4b3c2.ok
  · exact GGResIShape.D4b3c2w12.ok
  · exact GGResIShape.D4b3c2w21.ok

theorem case_D4_b3 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 4 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 4) i j) (hib : e 3 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_D4_b3 hcyc_D4_b3 shapes_D4_b3 vecs_D4_b3 hcand_D4_b3
    hshapes_D4_b3

theorem ggResI_type_D4 [Module.Finite (ZMod p) V] [Finite V]
    (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 4 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 4) i j) : GGResILinConcl p b CL CK g h α x := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact case_D4_b0 H e hCe hk
  · exact case_D4_b1 H e hCe hk
  · exact case_D4_b2 H e hCe hk
  · exact case_D4_b3 H e hCe hk

end CFSG.StandardType.GGResIDisp.D4
