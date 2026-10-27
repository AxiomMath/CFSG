module

public import CFSG.LocalAnalysis.StandardType.GGResIIDispatch
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A2b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A2b1c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A3b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A3b0c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A3b2c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A3b2c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A4b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A4b0c3
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A4b3c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A4b3c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A5b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A5b0c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A5b0c3
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A5b0c4
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A5b4c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A5b4c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A5b4c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A5b4c3
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A6b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A6b0c3
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A6b0c5
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A6b5c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A6b5c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A6b5c4
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A7b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A7b0c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A7b0c5
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A7b0c6
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A7b6c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A7b6c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A7b6c4
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A7b6c5
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A8b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A8b0c7
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A8b7c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.A8b7c6
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b0c3
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b0c4
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b3c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b3c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b3c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b3c4
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b4c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b4c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b4c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D5b4c3
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b5c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b5c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b5c4
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b5c6
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b6c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b6c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b6c4
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.D7b6c5
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.E6b0c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.E6b0c2
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.E6b1c0
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.E6b1c3
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.E6b1c5
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.E6b5c1
public import CFSG.LocalAnalysis.StandardType.GGResIIShape.E6b5c4

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggResII_tg_A2 : List (ℕ × ℕ × ℕ × ℕ) := [(2, 0, 0, 0)]

theorem ggResII_diag_A2 : ∀ i, (CartanMatrix.A 2) i i = 2 := by decide +kernel

theorem ggResII_htA_A2 : 2 ≤ 2 → ggInv (CartanMatrix.A 2) ∈ ggResII_tg_A2 :=
  fun _ => by decide +kernel

theorem ggResII_htD_A2 : 5 ≤ 2 → Odd 2 → ggInv (CartanMatrix.D 2) ∈ ggResII_tg_A2 :=
  fun h5 => absurd h5 (by norm_num)

theorem ggResII_htE_A2 : ∀ hn : 6 = 2, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_A2 :=
  fun hn => absurd hn (by norm_num)

theorem ggResII_cert_A2_0 : ∀ r : Fin 2 → Bool,
    ggInv (ggKmat (CartanMatrix.A 2) 0 r) ∈ ggResII_tg_A2 →
    ∃ ic ∈ ([1] : List (Fin 2)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A2_0 : ∀ ic ∈ ([1] : List (Fin 2)),
    GGResIIShapeOK (CartanMatrix.A 2) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl
  · exact GGResIIShape.A2b0c1.ok

theorem ggResII_cert_A2_1 : ∀ r : Fin 2 → Bool,
    ggInv (ggKmat (CartanMatrix.A 2) 1 r) ∈ ggResII_tg_A2 →
    ∃ ic ∈ ([0] : List (Fin 2)), ic ≠ 1 ∧ ∀ j, j ≠ 1 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A2_1 : ∀ ic ∈ ([0] : List (Fin 2)),
    GGResIIShapeOK (CartanMatrix.A 2) 1 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl
  · exact GGResIIShape.A2b1c0.ok

theorem ggResII_case_A2 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 2 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 2) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 2) ggResII_diag_A2 hib _ _
      ggResII_htA_A2 ggResII_htD_A2 ggResII_htE_A2 ggResII_cert_A2_0 ggResII_shapes_A2_0
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 2) ggResII_diag_A2 hib _ _
      ggResII_htA_A2 ggResII_htD_A2 ggResII_htE_A2 ggResII_cert_A2_1 ggResII_shapes_A2_1

@[expose] def ggResII_tg_A3 : List (ℕ × ℕ × ℕ × ℕ) := [(4, 0, 0, 0)]

theorem ggResII_diag_A3 : ∀ i, (CartanMatrix.A 3) i i = 2 := by decide +kernel

theorem ggResII_htA_A3 : 2 ≤ 3 → ggInv (CartanMatrix.A 3) ∈ ggResII_tg_A3 :=
  fun _ => by decide +kernel

theorem ggResII_htD_A3 : 5 ≤ 3 → Odd 3 → ggInv (CartanMatrix.D 3) ∈ ggResII_tg_A3 :=
  fun h5 => absurd h5 (by norm_num)

theorem ggResII_htE_A3 : ∀ hn : 6 = 3, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_A3 :=
  fun hn => absurd hn (by norm_num)

theorem ggResII_cert_A3_0 : ∀ r : Fin 3 → Bool,
    ggInv (ggKmat (CartanMatrix.A 3) 0 r) ∈ ggResII_tg_A3 →
    ∃ ic ∈ ([1, 2] : List (Fin 3)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A3_0 : ∀ ic ∈ ([1, 2] : List (Fin 3)),
    GGResIIShapeOK (CartanMatrix.A 3) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl
  · exact GGResIIShape.A3b0c1.ok
  · exact GGResIIShape.A3b0c2.ok

theorem ggResII_cert_A3_2 : ∀ r : Fin 3 → Bool,
    ggInv (ggKmat (CartanMatrix.A 3) 2 r) ∈ ggResII_tg_A3 →
    ∃ ic ∈ ([0, 1] : List (Fin 3)), ic ≠ 2 ∧ ∀ j, j ≠ 2 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A3_2 : ∀ ic ∈ ([0, 1] : List (Fin 3)),
    GGResIIShapeOK (CartanMatrix.A 3) 2 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl
  · exact GGResIIShape.A3b2c0.ok
  · exact GGResIIShape.A3b2c1.ok

theorem ggResII_case_A3 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 3 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 3) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 3) ggResII_diag_A3 hib _ _
      ggResII_htA_A3 ggResII_htD_A3 ggResII_htE_A3 ggResII_cert_A3_0 ggResII_shapes_A3_0
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 3)) 0 2 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 3) ggResII_diag_A3 hib _ _
      ggResII_htA_A3 ggResII_htD_A3 ggResII_htE_A3 ggResII_cert_A3_2 ggResII_shapes_A3_2

@[expose] def ggResII_tg_A4 : List (ℕ × ℕ × ℕ × ℕ) := [(6, 0, 0, 0)]

theorem ggResII_diag_A4 : ∀ i, (CartanMatrix.A 4) i i = 2 := by decide +kernel

theorem ggResII_htA_A4 : 2 ≤ 4 → ggInv (CartanMatrix.A 4) ∈ ggResII_tg_A4 :=
  fun _ => by decide +kernel

theorem ggResII_htD_A4 : 5 ≤ 4 → Odd 4 → ggInv (CartanMatrix.D 4) ∈ ggResII_tg_A4 :=
  fun h5 => absurd h5 (by norm_num)

theorem ggResII_htE_A4 : ∀ hn : 6 = 4, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_A4 :=
  fun hn => absurd hn (by norm_num)

theorem ggResII_cert_A4_0 : ∀ r : Fin 4 → Bool,
    ggInv (ggKmat (CartanMatrix.A 4) 0 r) ∈ ggResII_tg_A4 →
    ∃ ic ∈ ([1, 3] : List (Fin 4)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A4_0 : ∀ ic ∈ ([1, 3] : List (Fin 4)),
    GGResIIShapeOK (CartanMatrix.A 4) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl
  · exact GGResIIShape.A4b0c1.ok
  · exact GGResIIShape.A4b0c3.ok

theorem ggResII_cert_A4_3 : ∀ r : Fin 4 → Bool,
    ggInv (ggKmat (CartanMatrix.A 4) 3 r) ∈ ggResII_tg_A4 →
    ∃ ic ∈ ([0, 2] : List (Fin 4)), ic ≠ 3 ∧ ∀ j, j ≠ 3 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A4_3 : ∀ ic ∈ ([0, 2] : List (Fin 4)),
    GGResIIShapeOK (CartanMatrix.A 4) 3 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl
  · exact GGResIIShape.A4b3c0.ok
  · exact GGResIIShape.A4b3c2.ok

theorem ggResII_case_A4 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 4 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 4) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 4) ggResII_diag_A4 hib _ _
      ggResII_htA_A4 ggResII_htD_A4 ggResII_htE_A4 ggResII_cert_A4_0 ggResII_shapes_A4_0
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 4)) 0 2 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1} : Finset (Fin 4)) 1 3 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 4) ggResII_diag_A4 hib _ _
      ggResII_htA_A4 ggResII_htD_A4 ggResII_htE_A4 ggResII_cert_A4_3 ggResII_shapes_A4_3

@[expose] def ggResII_tg_A5 : List (ℕ × ℕ × ℕ × ℕ) := [(8, 0, 0, 0), (8, 1, 0, 2)]

theorem ggResII_diag_A5 : ∀ i, (CartanMatrix.A 5) i i = 2 := by decide +kernel

theorem ggResII_htA_A5 : 2 ≤ 5 → ggInv (CartanMatrix.A 5) ∈ ggResII_tg_A5 :=
  fun _ => by decide +kernel

theorem ggResII_htD_A5 : 5 ≤ 5 → Odd 5 → ggInv (CartanMatrix.D 5) ∈ ggResII_tg_A5 :=
  fun _ _ => by decide +kernel

theorem ggResII_htE_A5 : ∀ hn : 6 = 5, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_A5 :=
  fun hn => absurd hn (by norm_num)

theorem ggResII_cert_A5_0 : ∀ r : Fin 5 → Bool,
    ggInv (ggKmat (CartanMatrix.A 5) 0 r) ∈ ggResII_tg_A5 →
    ∃ ic ∈ ([1, 2, 3, 4] : List (Fin 5)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A5_0 : ∀ ic ∈ ([1, 2, 3, 4] : List (Fin 5)),
    GGResIIShapeOK (CartanMatrix.A 5) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl | rfl
  · exact GGResIIShape.A5b0c1.ok
  · exact GGResIIShape.A5b0c2.ok
  · exact GGResIIShape.A5b0c3.ok
  · exact GGResIIShape.A5b0c4.ok

theorem ggResII_cert_A5_4 : ∀ r : Fin 5 → Bool,
    ggInv (ggKmat (CartanMatrix.A 5) 4 r) ∈ ggResII_tg_A5 →
    ∃ ic ∈ ([0, 1, 2, 3] : List (Fin 5)), ic ≠ 4 ∧ ∀ j, j ≠ 4 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A5_4 : ∀ ic ∈ ([0, 1, 2, 3] : List (Fin 5)),
    GGResIIShapeOK (CartanMatrix.A 5) 4 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl | rfl
  · exact GGResIIShape.A5b4c0.ok
  · exact GGResIIShape.A5b4c1.ok
  · exact GGResIIShape.A5b4c2.ok
  · exact GGResIIShape.A5b4c3.ok

theorem ggResII_case_A5 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 5) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 5) ggResII_diag_A5 hib _ _
      ggResII_htA_A5 ggResII_htD_A5 ggResII_htE_A5 ggResII_cert_A5_0 ggResII_shapes_A5_0
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 5)) 0 2 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1} : Finset (Fin 5)) 1 3 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2} : Finset (Fin 5)) 2 4 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 5) ggResII_diag_A5 hib _ _
      ggResII_htA_A5 ggResII_htD_A5 ggResII_htE_A5 ggResII_cert_A5_4 ggResII_shapes_A5_4

@[expose] def ggResII_tg_A6 : List (ℕ × ℕ × ℕ × ℕ) := [(10, 0, 0, 0), (10, 1, 0, 1)]

theorem ggResII_diag_A6 : ∀ i, (CartanMatrix.A 6) i i = 2 := by decide +kernel

theorem ggResII_htA_A6 : 2 ≤ 6 → ggInv (CartanMatrix.A 6) ∈ ggResII_tg_A6 :=
  fun _ => by decide +kernel

theorem ggResII_htD_A6 : 5 ≤ 6 → Odd 6 → ggInv (CartanMatrix.D 6) ∈ ggResII_tg_A6 :=
  fun _ hodd => absurd hodd (by decide)

theorem ggResII_htE_A6 : ∀ hn : 6 = 6, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_A6 :=
  fun hn => by cases hn; decide +kernel

theorem ggResII_cert_A6_0 : ∀ r : Fin 6 → Bool,
    ggInv (ggKmat (CartanMatrix.A 6) 0 r) ∈ ggResII_tg_A6 →
    ∃ ic ∈ ([1, 3, 5] : List (Fin 6)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A6_0 : ∀ ic ∈ ([1, 3, 5] : List (Fin 6)),
    GGResIIShapeOK (CartanMatrix.A 6) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl
  · exact GGResIIShape.A6b0c1.ok
  · exact GGResIIShape.A6b0c3.ok
  · exact GGResIIShape.A6b0c5.ok

theorem ggResII_cert_A6_5 : ∀ r : Fin 6 → Bool,
    ggInv (ggKmat (CartanMatrix.A 6) 5 r) ∈ ggResII_tg_A6 →
    ∃ ic ∈ ([0, 2, 4] : List (Fin 6)), ic ≠ 5 ∧ ∀ j, j ≠ 5 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A6_5 : ∀ ic ∈ ([0, 2, 4] : List (Fin 6)),
    GGResIIShapeOK (CartanMatrix.A 6) 5 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl
  · exact GGResIIShape.A6b5c0.ok
  · exact GGResIIShape.A6b5c2.ok
  · exact GGResIIShape.A6b5c4.ok

theorem ggResII_case_A6 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 6) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 6) ggResII_diag_A6 hib _ _
      ggResII_htA_A6 ggResII_htD_A6 ggResII_htE_A6 ggResII_cert_A6_0 ggResII_shapes_A6_0
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 6)) 0 2 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1} : Finset (Fin 6)) 1 3 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2} : Finset (Fin 6)) 2 4 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2, 3} : Finset (Fin 6)) 3 5 (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 6) ggResII_diag_A6 hib _ _
      ggResII_htA_A6 ggResII_htD_A6 ggResII_htE_A6 ggResII_cert_A6_5 ggResII_shapes_A6_5

@[expose] def ggResII_tg_A7 : List (ℕ × ℕ × ℕ × ℕ) := [(12, 0, 0, 0), (12, 1, 0, 2)]

theorem ggResII_diag_A7 : ∀ i, (CartanMatrix.A 7) i i = 2 := by decide +kernel

theorem ggResII_htA_A7 : 2 ≤ 7 → ggInv (CartanMatrix.A 7) ∈ ggResII_tg_A7 :=
  fun _ => by decide +kernel

theorem ggResII_htD_A7 : 5 ≤ 7 → Odd 7 → ggInv (CartanMatrix.D 7) ∈ ggResII_tg_A7 :=
  fun _ _ => by decide +kernel

theorem ggResII_htE_A7 : ∀ hn : 6 = 7, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_A7 :=
  fun hn => absurd hn (by norm_num)

theorem ggResII_cert_A7_0 : ∀ r : Fin 7 → Bool,
    ggInv (ggKmat (CartanMatrix.A 7) 0 r) ∈ ggResII_tg_A7 →
    ∃ ic ∈ ([1, 2, 5, 6] : List (Fin 7)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A7_0 : ∀ ic ∈ ([1, 2, 5, 6] : List (Fin 7)),
    GGResIIShapeOK (CartanMatrix.A 7) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl | rfl
  · exact GGResIIShape.A7b0c1.ok
  · exact GGResIIShape.A7b0c2.ok
  · exact GGResIIShape.A7b0c5.ok
  · exact GGResIIShape.A7b0c6.ok

theorem ggResII_cert_A7_6 : ∀ r : Fin 7 → Bool,
    ggInv (ggKmat (CartanMatrix.A 7) 6 r) ∈ ggResII_tg_A7 →
    ∃ ic ∈ ([0, 1, 4, 5] : List (Fin 7)), ic ≠ 6 ∧ ∀ j, j ≠ 6 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A7_6 : ∀ ic ∈ ([0, 1, 4, 5] : List (Fin 7)),
    GGResIIShapeOK (CartanMatrix.A 7) 6 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl | rfl
  · exact GGResIIShape.A7b6c0.ok
  · exact GGResIIShape.A7b6c1.ok
  · exact GGResIIShape.A7b6c4.ok
  · exact GGResIIShape.A7b6c5.ok

theorem ggResII_case_A7 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 7) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 7) ggResII_diag_A7 hib _ _
      ggResII_htA_A7 ggResII_htD_A7 ggResII_htE_A7 ggResII_cert_A7_0 ggResII_shapes_A7_0
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 7)) 0 2 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1} : Finset (Fin 7)) 1 3 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2} : Finset (Fin 7)) 2 4 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2, 3} : Finset (Fin 7)) 3 5 (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2, 3, 4} : Finset (Fin 7)) 4 6 (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 7) ggResII_diag_A7 hib _ _
      ggResII_htA_A7 ggResII_htD_A7 ggResII_htE_A7 ggResII_cert_A7_6 ggResII_shapes_A7_6

@[expose] def ggResII_tg_A8 : List (ℕ × ℕ × ℕ × ℕ) := [(14, 0, 0, 0)]

theorem ggResII_diag_A8 : ∀ i, (CartanMatrix.A 8) i i = 2 := by decide +kernel

theorem ggResII_htA_A8 : 2 ≤ 8 → ggInv (CartanMatrix.A 8) ∈ ggResII_tg_A8 :=
  fun _ => by decide +kernel

theorem ggResII_htD_A8 : 5 ≤ 8 → Odd 8 → ggInv (CartanMatrix.D 8) ∈ ggResII_tg_A8 :=
  fun _ hodd => absurd hodd (by decide)

theorem ggResII_htE_A8 : ∀ hn : 6 = 8, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_A8 :=
  fun hn => absurd hn (by norm_num)

theorem ggResII_cert_A8_0 : ∀ r : Fin 8 → Bool,
    ggInv (ggKmat (CartanMatrix.A 8) 0 r) ∈ ggResII_tg_A8 →
    ∃ ic ∈ ([1, 7] : List (Fin 8)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A8_0 : ∀ ic ∈ ([1, 7] : List (Fin 8)),
    GGResIIShapeOK (CartanMatrix.A 8) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl
  · exact GGResIIShape.A8b0c1.ok
  · exact GGResIIShape.A8b0c7.ok

theorem ggResII_cert_A8_7 : ∀ r : Fin 8 → Bool,
    ggInv (ggKmat (CartanMatrix.A 8) 7 r) ∈ ggResII_tg_A8 →
    ∃ ic ∈ ([0, 6] : List (Fin 8)), ic ≠ 7 ∧ ∀ j, j ≠ 7 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_A8_7 : ∀ ic ∈ ([0, 6] : List (Fin 8)),
    GGResIIShapeOK (CartanMatrix.A 8) 7 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl
  · exact GGResIIShape.A8b7c0.ok
  · exact GGResIIShape.A8b7c6.ok

theorem ggResII_case_A8 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 8 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.A 8) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 8) ggResII_diag_A8 hib _ _
      ggResII_htA_A8 ggResII_htD_A8 ggResII_htE_A8 ggResII_cert_A8_0 ggResII_shapes_A8_0
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 8)) 0 2 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1} : Finset (Fin 8)) 1 3 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2} : Finset (Fin 8)) 2 4 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2, 3} : Finset (Fin 8)) 3 5 (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2, 3, 4} : Finset (Fin 8)) 4 6 (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2, 3, 4, 5} : Finset (Fin 8)) 5 7 (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_A 8) ggResII_diag_A8 hib _ _
      ggResII_htA_A8 ggResII_htD_A8 ggResII_htE_A8 ggResII_cert_A8_7 ggResII_shapes_A8_7

@[expose] def ggResII_tg_D5 : List (ℕ × ℕ × ℕ × ℕ) := [(8, 0, 0, 0), (8, 1, 0, 2)]

theorem ggResII_diag_D5 : ∀ i, (CartanMatrix.D 5) i i = 2 := by decide +kernel

theorem ggResII_htA_D5 : 2 ≤ 5 → ggInv (CartanMatrix.A 5) ∈ ggResII_tg_D5 :=
  fun _ => by decide +kernel

theorem ggResII_htD_D5 : 5 ≤ 5 → Odd 5 → ggInv (CartanMatrix.D 5) ∈ ggResII_tg_D5 :=
  fun _ _ => by decide +kernel

theorem ggResII_htE_D5 : ∀ hn : 6 = 5, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_D5 :=
  fun hn => absurd hn (by norm_num)

theorem ggResII_cert_D5_0 : ∀ r : Fin 5 → Bool,
    ggInv (ggKmat (CartanMatrix.D 5) 0 r) ∈ ggResII_tg_D5 →
    ∃ ic ∈ ([1, 3, 4] : List (Fin 5)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_D5_0 : ∀ ic ∈ ([1, 3, 4] : List (Fin 5)),
    GGResIIShapeOK (CartanMatrix.D 5) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl
  · exact GGResIIShape.D5b0c1.ok
  · exact GGResIIShape.D5b0c3.ok
  · exact GGResIIShape.D5b0c4.ok

theorem ggResII_cert_D5_3 : ∀ r : Fin 5 → Bool,
    ggInv (ggKmat (CartanMatrix.D 5) 3 r) ∈ ggResII_tg_D5 →
    ∃ ic ∈ ([0, 1, 2, 4] : List (Fin 5)), ic ≠ 3 ∧ ∀ j, j ≠ 3 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_D5_3 : ∀ ic ∈ ([0, 1, 2, 4] : List (Fin 5)),
    GGResIIShapeOK (CartanMatrix.D 5) 3 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl | rfl
  · exact GGResIIShape.D5b3c0.ok
  · exact GGResIIShape.D5b3c1.ok
  · exact GGResIIShape.D5b3c2.ok
  · exact GGResIIShape.D5b3c4.ok

theorem ggResII_cert_D5_4 : ∀ r : Fin 5 → Bool,
    ggInv (ggKmat (CartanMatrix.D 5) 4 r) ∈ ggResII_tg_D5 →
    ∃ ic ∈ ([0, 1, 2, 3] : List (Fin 5)), ic ≠ 4 ∧ ∀ j, j ≠ 4 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_D5_4 : ∀ ic ∈ ([0, 1, 2, 3] : List (Fin 5)),
    GGResIIShapeOK (CartanMatrix.D 5) 4 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl | rfl
  · exact GGResIIShape.D5b4c0.ok
  · exact GGResIIShape.D5b4c1.ok
  · exact GGResIIShape.D5b4c2.ok
  · exact GGResIIShape.D5b4c3.ok

theorem ggResII_case_D5 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 5) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_D 5) ggResII_diag_D5 hib _ _
      ggResII_htA_D5 ggResII_htD_D5 ggResII_htE_D5 ggResII_cert_D5_0 ggResII_shapes_D5_0
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 5)) 0 2 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1} : Finset (Fin 5)) 1 3 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_D 5) ggResII_diag_D5 hib _ _
      ggResII_htA_D5 ggResII_htD_D5 ggResII_htE_D5 ggResII_cert_D5_3 ggResII_shapes_D5_3
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_D 5) ggResII_diag_D5 hib _ _
      ggResII_htA_D5 ggResII_htD_D5 ggResII_htE_D5 ggResII_cert_D5_4 ggResII_shapes_D5_4

@[expose] def ggResII_tg_D7 : List (ℕ × ℕ × ℕ × ℕ) := [(12, 0, 0, 0), (12, 1, 0, 2)]

theorem ggResII_diag_D7 : ∀ i, (CartanMatrix.D 7) i i = 2 := by decide +kernel

theorem ggResII_htA_D7 : 2 ≤ 7 → ggInv (CartanMatrix.A 7) ∈ ggResII_tg_D7 :=
  fun _ => by decide +kernel

theorem ggResII_htD_D7 : 5 ≤ 7 → Odd 7 → ggInv (CartanMatrix.D 7) ∈ ggResII_tg_D7 :=
  fun _ _ => by decide +kernel

theorem ggResII_htE_D7 : ∀ hn : 6 = 7, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_D7 :=
  fun hn => absurd hn (by norm_num)

theorem ggResII_cert_D7_0 : ∀ r : Fin 7 → Bool,
    ggInv (ggKmat (CartanMatrix.D 7) 0 r) ∈ ggResII_tg_D7 →
    ∃ ic ∈ ([1] : List (Fin 7)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_D7_0 : ∀ ic ∈ ([1] : List (Fin 7)),
    GGResIIShapeOK (CartanMatrix.D 7) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl
  · exact GGResIIShape.D7b0c1.ok

theorem ggResII_cert_D7_5 : ∀ r : Fin 7 → Bool,
    ggInv (ggKmat (CartanMatrix.D 7) 5 r) ∈ ggResII_tg_D7 →
    ∃ ic ∈ ([0, 1, 4, 6] : List (Fin 7)), ic ≠ 5 ∧ ∀ j, j ≠ 5 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_D7_5 : ∀ ic ∈ ([0, 1, 4, 6] : List (Fin 7)),
    GGResIIShapeOK (CartanMatrix.D 7) 5 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl | rfl
  · exact GGResIIShape.D7b5c0.ok
  · exact GGResIIShape.D7b5c1.ok
  · exact GGResIIShape.D7b5c4.ok
  · exact GGResIIShape.D7b5c6.ok

theorem ggResII_cert_D7_6 : ∀ r : Fin 7 → Bool,
    ggInv (ggKmat (CartanMatrix.D 7) 6 r) ∈ ggResII_tg_D7 →
    ∃ ic ∈ ([0, 1, 4, 5] : List (Fin 7)), ic ≠ 6 ∧ ∀ j, j ≠ 6 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_D7_6 : ∀ ic ∈ ([0, 1, 4, 5] : List (Fin 7)),
    GGResIIShapeOK (CartanMatrix.D 7) 6 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl | rfl
  · exact GGResIIShape.D7b6c0.ok
  · exact GGResIIShape.D7b6c1.ok
  · exact GGResIIShape.D7b6c4.ok
  · exact GGResIIShape.D7b6c5.ok

theorem ggResII_case_D7 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.D 7) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_D 7) ggResII_diag_D7 hib _ _
      ggResII_htA_D7 ggResII_htD_D7 ggResII_htE_D7 ggResII_cert_D7_0 ggResII_shapes_D7_0
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 7)) 0 2 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1} : Finset (Fin 7)) 1 3 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2} : Finset (Fin 7)) 2 4 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2, 3} : Finset (Fin 7)) 3 5 (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_D 7) ggResII_diag_D7 hib _ _
      ggResII_htA_D7 ggResII_htD_D7 ggResII_htE_D7 ggResII_cert_D7_5 ggResII_shapes_D7_5
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_D 7) ggResII_diag_D7 hib _ _
      ggResII_htA_D7 ggResII_htD_D7 ggResII_htE_D7 ggResII_cert_D7_6 ggResII_shapes_D7_6

@[expose] def ggResII_tg_E6 : List (ℕ × ℕ × ℕ × ℕ) := [(10, 0, 0, 0), (10, 1, 0, 1)]

theorem ggResII_diag_E6 : ∀ i, (CartanMatrix.E 6) i i = 2 := by decide +kernel

theorem ggResII_htA_E6 : 2 ≤ 6 → ggInv (CartanMatrix.A 6) ∈ ggResII_tg_E6 :=
  fun _ => by decide +kernel

theorem ggResII_htD_E6 : 5 ≤ 6 → Odd 6 → ggInv (CartanMatrix.D 6) ∈ ggResII_tg_E6 :=
  fun _ hodd => absurd hodd (by decide)

theorem ggResII_htE_E6 : ∀ hn : 6 = 6, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm)
    (Fin.cast hn.symm)) ∈ ggResII_tg_E6 :=
  fun hn => by cases hn; decide +kernel

theorem ggResII_cert_E6_0 : ∀ r : Fin 6 → Bool,
    ggInv (ggKmat (CartanMatrix.E 6) 0 r) ∈ ggResII_tg_E6 →
    ∃ ic ∈ ([1, 2] : List (Fin 6)), ic ≠ 0 ∧ ∀ j, j ≠ 0 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_E6_0 : ∀ ic ∈ ([1, 2] : List (Fin 6)),
    GGResIIShapeOK (CartanMatrix.E 6) 0 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl
  · exact GGResIIShape.E6b0c1.ok
  · exact GGResIIShape.E6b0c2.ok

theorem ggResII_cert_E6_1 : ∀ r : Fin 6 → Bool,
    ggInv (ggKmat (CartanMatrix.E 6) 1 r) ∈ ggResII_tg_E6 →
    ∃ ic ∈ ([0, 3, 5] : List (Fin 6)), ic ≠ 1 ∧ ∀ j, j ≠ 1 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_E6_1 : ∀ ic ∈ ([0, 3, 5] : List (Fin 6)),
    GGResIIShapeOK (CartanMatrix.E 6) 1 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl | rfl
  · exact GGResIIShape.E6b1c0.ok
  · exact GGResIIShape.E6b1c3.ok
  · exact GGResIIShape.E6b1c5.ok

theorem ggResII_cert_E6_5 : ∀ r : Fin 6 → Bool,
    ggInv (ggKmat (CartanMatrix.E 6) 5 r) ∈ ggResII_tg_E6 →
    ∃ ic ∈ ([1, 4] : List (Fin 6)), ic ≠ 5 ∧ ∀ j, j ≠ 5 → r j = decide (j = ic) := by
  decide +kernel

theorem ggResII_shapes_E6_5 : ∀ ic ∈ ([1, 4] : List (Fin 6)),
    GGResIIShapeOK (CartanMatrix.E 6) 5 ic := by
  intro ic hic
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
  rcases hic with rfl | rfl
  · exact GGResIIShape.E6b5c1.ok
  · exact GGResIIShape.E6b5c4.ok

theorem ggResII_case_E6 {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}
    (H : GGResIIHyp p b ML CL CK g h α x y) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = (CartanMatrix.E 6) i j) : GGResIIFConcl p b g h α := by
  obtain ⟨ib, hib⟩ : ∃ ib, e ib = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases ib
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_E 6) ggResII_diag_E6 hib _ _
      ggResII_htA_E6 ggResII_htD_E6 ggResII_htE_E6 ggResII_cert_E6_0 ggResII_shapes_E6_0
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_E 6) ggResII_diag_E6 hib _ _
      ggResII_htA_E6 ggResII_htD_E6 ggResII_htE_E6 ggResII_cert_E6_1 ggResII_shapes_E6_1
  · exact ggResII_dispatch_cut H e hCe hib ({0} : Finset (Fin 6)) 0 1 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({1} : Finset (Fin 6)) 1 0 (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_cut H e hCe hib ({0, 1, 2, 3} : Finset (Fin 6)) 3 5 (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact ggResII_dispatch_leaf H e hCe (CartanMatrix.isSimplyLaced_E 6) ggResII_diag_E6 hib _ _
      ggResII_htA_E6 ggResII_htD_E6 ggResII_htE_E6 ggResII_cert_E6_5 ggResII_shapes_E6_5

theorem ggResIILinNonegInput_holds : GGResIILinNonegInput := by
  intro p _ Λ _ _ b ML CL MK CK V _ _ _ g h α x y hp2 hcard _ hCL _ _ hLt hKt hconn hg hL hK hLI
    hdep hxL hfix hxa hyK hyx
  have H : GGResIIHyp p b ML CL CK g h α x y :=
    ⟨hp2, hCL, hKt, hconn, hg, hL, hK, hLI, hdep, hxL, hfix, hxa, hyK, hyx⟩
  show GGResIIFConcl p b g h α
  rcases hLt with ⟨n, e, hn, hCe⟩ | ⟨n, e, hn, hodd, hCe⟩ | ⟨e, hCe⟩
  · have hn8 : n ≤ 8 := by
      have := Fintype.card_congr e
      rw [Fintype.card_fin] at this
      omega
    interval_cases n
    · exact ggResII_case_A2 H e hCe
    · exact ggResII_case_A3 H e hCe
    · exact ggResII_case_A4 H e hCe
    · exact ggResII_case_A5 H e hCe
    · exact ggResII_case_A6 H e hCe
    · exact ggResII_case_A7 H e hCe
    · exact ggResII_case_A8 H e hCe
  · have hn8 : n ≤ 8 := by
      have := Fintype.card_congr e
      rw [Fintype.card_fin] at this
      omega
    interval_cases n
    · exact ggResII_case_D5 H e hCe
    · exact absurd hodd (by decide)
    · exact ggResII_case_D7 H e hCe
    · exact absurd hodd (by decide)
  · exact ggResII_case_E6 H e hCe

end CFSG.StandardType
