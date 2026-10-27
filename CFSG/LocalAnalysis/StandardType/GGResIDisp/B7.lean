module

public import CFSG.LocalAnalysis.StandardType.GGResIDispatch
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c0w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c0w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c1
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c2
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c3
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c4
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c5
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c5w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.B7b6c5w21

public section

namespace CFSG.StandardType.GGResIDisp.B7

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
  {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V} {x : V}

@[expose] def pt_B7_b0 : Fin 7 → Fin 7 → List (Fin 7) :=
  fun j₁ j₂ => (([[[], [], [], [], [], [], []], [[], [], [2, 1], [3, 2, 1], [4, 3, 2, 1], [5, 4, 3, 2, 1], [6, 5, 4, 3, 2, 1]], [[], [1, 2], [], [3, 2], [4, 3, 2], [5, 4, 3, 2], [6, 5, 4, 3, 2]], [[], [1, 2, 3], [2, 3], [], [4, 3], [5, 4, 3], [6, 5, 4, 3]], [[], [1, 2, 3, 4], [2, 3, 4], [3, 4], [], [5, 4], [6, 5, 4]], [[], [1, 2, 3, 4, 5], [2, 3, 4, 5], [3, 4, 5], [4, 5], [], [6, 5]], [[], [1, 2, 3, 4, 5, 6], [2, 3, 4, 5, 6], [3, 4, 5, 6], [4, 5, 6], [5, 6], []]] : List (List (List (Fin 7)))).getD j₁ []).getD j₂ []

theorem hcyc_B7_b0 : ∀ j₁ j₂ : Fin 7, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.B 7) 0 j₁ j₂ (pt_B7_b0 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_B7_b0 : List (Fin 7 × ℤ × ℤ) := []

@[expose] def vecs_B7_b0 : List (Fin 7 × ℤ × ℤ × List ℕ) :=
  [(1, -1, -2, [1, 2, 2, 2, 2, 2, 1]),
   (1, -2, -1, [2, 2, 2, 2, 2, 2, 1]),
   (1, -1, -3, [1, 2, 2, 2, 2, 2, 1]),
   (1, -3, -1, [2, 2, 2, 2, 2, 2, 1]),
   (2, -1, -1, [1, 1, 2, 2, 2, 2, 1]),
   (2, -1, -2, [1, 1, 2, 2, 2, 2, 1]),
   (2, -2, -1, [1, 1, 2, 2, 2, 2, 1]),
   (2, -1, -3, [1, 1, 2, 2, 2, 2, 1]),
   (2, -3, -1, [1, 1, 2, 2, 2, 2, 1]),
   (3, -1, -1, [2, 1, 2, 4, 4, 4, 2]),
   (3, -1, -2, [1, 1, 2, 3, 2, 2, 1]),
   (3, -2, -1, [2, 1, 2, 3, 2, 2, 1]),
   (3, -1, -3, [1, 1, 2, 3, 2, 2, 1]),
   (3, -3, -1, [2, 1, 2, 3, 2, 2, 1]),
   (4, -1, -1, [2, 1, 2, 3, 4, 3, 1]),
   (4, -1, -2, [2, 1, 2, 3, 4, 2, 1]),
   (4, -2, -1, [3, 1, 2, 3, 4, 2, 1]),
   (4, -1, -3, [1, 1, 2, 3, 4, 2, 1]),
   (4, -3, -1, [3, 1, 2, 3, 4, 2, 1]),
   (5, -1, -1, [2, 1, 2, 3, 4, 5, 2]),
   (5, -1, -2, [2, 1, 2, 3, 4, 5, 1]),
   (5, -2, -1, [2, 1, 2, 3, 4, 5, 2]),
   (5, -1, -3, [1, 1, 2, 3, 4, 5, 2]),
   (5, -3, -1, [2, 1, 2, 3, 4, 5, 2]),
   (6, -1, -1, [1, 1, 2, 3, 4, 5, 3]),
   (6, -1, -2, [1, 1, 2, 3, 4, 5, 3]),
   (6, -2, -1, [1, 1, 2, 3, 4, 5, 3]),
   (6, -1, -3, [1, 1, 2, 3, 4, 5, 3]),
   (6, -3, -1, [1, 1, 2, 3, 4, 5, 3])]

theorem hcand_B7_b0 : ∀ ic : Fin 7, ic ≠ 0 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.B 7) 0 ic pr.1 pr.2 shapes_B7_b0 vecs_B7_b0 = true := by
  decide +kernel

theorem hshapes_B7_b0 : ∀ s ∈ shapes_B7_b0, GGResIShapeOK (CartanMatrix.B 7) 0 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp [shapes_B7_b0] at hs

theorem case_B7_b0 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 7 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 7) i j) (hib : e 0 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 1 (by decide) pt_B7_b0 hcyc_B7_b0 shapes_B7_b0 vecs_B7_b0 hcand_B7_b0
    hshapes_B7_b0

theorem case_B7_b1 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 7) i j) (hib : e 1 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0} 0 2 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_B7_b2 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 7) i j) (hib : e 2 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1} 1 3 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_B7_b3 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 7) i j) (hib : e 3 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1, 2} 2 4 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_B7_b4 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 7) i j) (hib : e 4 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1, 2, 3} 3 5 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

theorem case_B7_b5 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 7) i j) (hib : e 5 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0, 1, 2, 3, 4} 4 6 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

@[expose] def pt_B7_b6 : Fin 7 → Fin 7 → List (Fin 7) :=
  fun j₁ j₂ => (([[[], [1, 0], [2, 1, 0], [3, 2, 1, 0], [4, 3, 2, 1, 0], [5, 4, 3, 2, 1, 0], []], [[0, 1], [], [2, 1], [3, 2, 1], [4, 3, 2, 1], [5, 4, 3, 2, 1], []], [[0, 1, 2], [1, 2], [], [3, 2], [4, 3, 2], [5, 4, 3, 2], []], [[0, 1, 2, 3], [1, 2, 3], [2, 3], [], [4, 3], [5, 4, 3], []], [[0, 1, 2, 3, 4], [1, 2, 3, 4], [2, 3, 4], [3, 4], [], [5, 4], []], [[0, 1, 2, 3, 4, 5], [1, 2, 3, 4, 5], [2, 3, 4, 5], [3, 4, 5], [4, 5], [], []], [[], [], [], [], [], [], []]] : List (List (List (Fin 7)))).getD j₁ []).getD j₂ []

theorem hcyc_B7_b6 : ∀ j₁ j₂ : Fin 7, j₁ ≠ 6 → j₂ ≠ 6 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.B 7) 6 j₁ j₂ (pt_B7_b6 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_B7_b6 : List (Fin 7 × ℤ × ℤ) := [(0, -1, -1), (0, -1, -2), (0, -2, -1), (1, -1, -1), (2, -1, -1), (3, -1, -1), (4, -1, -1), (5, -1, -1), (5, -1, -2), (5, -2, -1)]

@[expose] def vecs_B7_b6 : List (Fin 7 × ℤ × ℤ × List ℕ) :=
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

theorem hcand_B7_b6 : ∀ ic : Fin 7, ic ≠ 6 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.B 7) 6 ic pr.1 pr.2 shapes_B7_b6 vecs_B7_b6 = true := by
  decide +kernel

theorem hshapes_B7_b6 : ∀ s ∈ shapes_B7_b6, GGResIShapeOK (CartanMatrix.B 7) 6 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_B7_b6, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.B7b6c0.ok
  · exact GGResIShape.B7b6c0w12.ok
  · exact GGResIShape.B7b6c0w21.ok
  · exact GGResIShape.B7b6c1.ok
  · exact GGResIShape.B7b6c2.ok
  · exact GGResIShape.B7b6c3.ok
  · exact GGResIShape.B7b6c4.ok
  · exact GGResIShape.B7b6c5.ok
  · exact GGResIShape.B7b6c5w12.ok
  · exact GGResIShape.B7b6c5w21.ok

theorem case_B7_b6 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 7 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 7) i j) (hib : e 6 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_B7_b6 hcyc_B7_b6 shapes_B7_b6 vecs_B7_b6 hcand_B7_b6
    hshapes_B7_b6

theorem ggResI_type_B7 [Module.Finite (ZMod p) V] [Finite V]
    (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 7 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.B 7) i j) : GGResILinConcl p b CL CK g h α x := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact case_B7_b0 H e hCe hk
  · exact case_B7_b1 H e hCe hk
  · exact case_B7_b2 H e hCe hk
  · exact case_B7_b3 H e hCe hk
  · exact case_B7_b4 H e hCe hk
  · exact case_B7_b5 H e hCe hk
  · exact case_B7_b6 H e hCe hk

end CFSG.StandardType.GGResIDisp.B7
