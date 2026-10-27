module

public import CFSG.LocalAnalysis.StandardType.GGResIDispatch
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b0c1w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b0c1w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b0c2
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b0c2w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b0c2w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b2c0
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b2c0w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b2c0w21
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b2c1w12
public import CFSG.LocalAnalysis.StandardType.GGResIShape.A3b2c1w21

public section

namespace CFSG.StandardType.GGResIDisp.A3

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
  {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V} {x : V}

@[expose] def pt_A3_b0 : Fin 3 → Fin 3 → List (Fin 3) :=
  fun j₁ j₂ => (([[[], [], []], [[], [], [2, 1]], [[], [1, 2], []]] : List (List (List (Fin 3)))).getD j₁ []).getD j₂ []

theorem hcyc_A3_b0 : ∀ j₁ j₂ : Fin 3, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.A 3) 0 j₁ j₂ (pt_A3_b0 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_A3_b0 : List (Fin 3 × ℤ × ℤ) := [(1, -1, -2), (1, -2, -1), (2, -1, -1), (2, -1, -2), (2, -2, -1)]

@[expose] def vecs_A3_b0 : List (Fin 3 × ℤ × ℤ × List ℕ) :=
  [(1, -1, -3, [1, 2, 1]),
   (1, -3, -1, [3, 2, 1]),
   (2, -1, -3, [1, 1, 2]),
   (2, -3, -1, [3, 1, 2])]

theorem hcand_A3_b0 : ∀ ic : Fin 3, ic ≠ 0 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.A 3) 0 ic pr.1 pr.2 shapes_A3_b0 vecs_A3_b0 = true := by
  decide +kernel

theorem hshapes_A3_b0 : ∀ s ∈ shapes_A3_b0, GGResIShapeOK (CartanMatrix.A 3) 0 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_A3_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.A3b0c1w12.ok
  · exact GGResIShape.A3b0c1w21.ok
  · exact GGResIShape.A3b0c2.ok
  · exact GGResIShape.A3b0c2w12.ok
  · exact GGResIShape.A3b0c2w21.ok

theorem case_A3_b0 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 3 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 3) i j) (hib : e 0 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 1 (by decide) pt_A3_b0 hcyc_A3_b0 shapes_A3_b0 vecs_A3_b0 hcand_A3_b0
    hshapes_A3_b0

theorem case_A3_b1 [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) (e : Fin 3 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 3) i j) (hib : e 1 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_cut H e hCe hib {0} 0 2 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

@[expose] def pt_A3_b2 : Fin 3 → Fin 3 → List (Fin 3) :=
  fun j₁ j₂ => (([[[], [1, 0], []], [[0, 1], [], []], [[], [], []]] : List (List (List (Fin 3)))).getD j₁ []).getD j₂ []

theorem hcyc_A3_b2 : ∀ j₁ j₂ : Fin 3, j₁ ≠ 2 → j₂ ≠ 2 → j₁ ≠ j₂ →
    ggCycleOK (CartanMatrix.A 3) 2 j₁ j₂ (pt_A3_b2 j₁ j₂) := by
  decide +kernel

@[expose] def shapes_A3_b2 : List (Fin 3 × ℤ × ℤ) := [(0, -1, -1), (0, -1, -2), (0, -2, -1), (1, -1, -2), (1, -2, -1)]

@[expose] def vecs_A3_b2 : List (Fin 3 × ℤ × ℤ × List ℕ) :=
  [(0, -1, -3, [2, 1, 1]),
   (0, -3, -1, [2, 1, 3]),
   (1, -1, -3, [1, 2, 1]),
   (1, -3, -1, [1, 2, 3])]

theorem hcand_A3_b2 : ∀ ic : Fin 3, ic ≠ 2 → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB (CartanMatrix.A 3) 2 ic pr.1 pr.2 shapes_A3_b2 vecs_A3_b2 = true := by
  decide +kernel

theorem hshapes_A3_b2 : ∀ s ∈ shapes_A3_b2, GGResIShapeOK (CartanMatrix.A 3) 2 s.1 s.2.1 s.2.2 := by
  intro s hs
  simp only [shapes_A3_b2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact GGResIShape.A3b2c0.ok
  · exact GGResIShape.A3b2c0w12.ok
  · exact GGResIShape.A3b2c0w21.ok
  · exact GGResIShape.A3b2c1w12.ok
  · exact GGResIShape.A3b2c1w21.ok

theorem case_A3_b2 [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 3 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 3) i j) (hib : e 2 = b) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_leaf H e hCe hib 0 (by decide) pt_A3_b2 hcyc_A3_b2 shapes_A3_b2 vecs_A3_b2 hcand_A3_b2
    hshapes_A3_b2

theorem ggResI_type_A3 [Module.Finite (ZMod p) V] [Finite V]
    (H : GGResIHyp p b ML CL MK CK g h α x)
    (e : Fin 3 ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 3) i j) : GGResILinConcl p b CL CK g h α x := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact case_A3_b0 H e hCe hk
  · exact case_A3_b1 H e hCe hk
  · exact case_A3_b2 H e hCe hk

end CFSG.StandardType.GGResIDisp.A3
