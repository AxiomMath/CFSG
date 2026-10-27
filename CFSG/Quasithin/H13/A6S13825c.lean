module

public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.H13.A6.L4Ind

open Matrix

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

abbrev V4 : Type := Fin 4 → ZMod 2

abbrev SL4 : Type := Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)

abbrev InL0 (v : V4) : Prop := v 2 = 0 ∧ v 3 = 0

abbrev InQ2 (m : M4) : Prop := m 2 0 = 0 ∧ m 3 0 = 0 ∧ m 2 1 = 0 ∧ m 3 1 = 0

abbrev e0 : V4 := ![1, 0, 0, 0]

abbrev e1 : V4 := ![0, 1, 0, 0]

abbrev e2 : V4 := ![0, 0, 1, 0]

theorem zmod2_eq_one_of_mul : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by
  decide

theorem det_eq_one_of_mul {m n : M4} (h : m * n = 1) : m.det = 1 :=
  zmod2_eq_one_of_mul _ n.det (by rw [← det_mul, h, det_one])

@[expose] def mkSL (m n : M4) (h : m * n = 1) : SL4 := ⟨m, det_eq_one_of_mul h⟩

theorem coe_mkSL (m n : M4) (h : m * n = 1) : ((mkSL m n h : SL4) : M4) = m := rfl

theorem coe_mkSL_inv (m n : M4) (h : m * n = 1) : (((mkSL m n h)⁻¹ : SL4) : M4) = n := by
  have h' : mkSL m n h * mkSL n m (mul_eq_one_comm.mp h) = 1 :=
    Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_mkSL, coe_mkSL]
      exact h)
  rw [inv_eq_of_mul_eq_one_right h']
  rfl

theorem inv_mulVec_mulVec (g : SL4) (v : V4) : ((g⁻¹ : SL4) : M4) *ᵥ ((g : M4) *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem mulVec_inv_mulVec (g : SL4) (v : V4) : (g : M4) *ᵥ (((g⁻¹ : SL4) : M4) *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

abbrev g0M : M4 := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

@[expose] def g0 : SL4 := mkSL g0M g0M (by decide)

theorem g0_mul_self : g0 * g0 = 1 := Subtype.ext (by decide)

abbrev s01M : M4 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

abbrev t01M : M4 := !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

abbrev rBM (b : Fin 2 → Fin 2 → ZMod 2) : M4 :=
  !![1, 0, b 0 0, b 0 1; 0, 1, b 1 0, b 1 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem rBM_add : ∀ b c : Fin 2 → Fin 2 → ZMod 2, rBM (b + c) = rBM b * rBM c := by
  decide

theorem rBM_mul_self : ∀ b : Fin 2 → Fin 2 → ZMod 2, rBM b * rBM b = 1 := by
  decide

@[expose] def rB (b : Fin 2 → Fin 2 → ZMod 2) : SL4 := mkSL (rBM b) (rBM b) (rBM_mul_self b)

theorem rB_add (b c : Fin 2 → Fin 2 → ZMod 2) : rB (b + c) = rB b * rB c :=
  Subtype.ext (rBM_add b c)

theorem rB_zero : rB 0 = 1 := Subtype.ext (by decide)

theorem rB_injective : Function.Injective rB := by
  intro b c h
  have h1 : rBM b = rBM c := congrArg Subtype.val h
  have key : ∀ b c : Fin 2 → Fin 2 → ZMod 2, rBM b = rBM c → b = c := by decide
  exact key b c h1

theorem mulVec_e0 (m : M4) : m *ᵥ e0 = fun i => m i 0 := by
  ext i
  simp [mulVec, dotProduct, Fin.sum_univ_four]

theorem mulVec_e1 (m : M4) : m *ᵥ e1 = fun i => m i 1 := by
  ext i
  simp [mulVec, dotProduct, Fin.sum_univ_four]

theorem inQ2_iff (m : M4) : InQ2 m ↔ InL0 (m *ᵥ e0) ∧ InL0 (m *ᵥ e1) := by
  rw [mulVec_e0, mulVec_e1]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩, fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩⟩

theorem inL0_cases : ∀ z : V4, InL0 z → z = 0 ∨ z = e0 ∨ z = e1 ∨ z = e0 + e1 := by
  decide

@[expose] def pList : List (M4 × M4) :=
  [(!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]),
   (!![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0],
    !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]),
   (!![1,0,1,0; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,0,1,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]),
   (!![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1],
    !![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1]),
   (!![1,0,0,1; 0,1,0,0; 0,0,0,1; 0,0,1,0],
    !![1,0,1,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]),
   (!![1,0,0,0; 0,1,0,1; 0,0,0,1; 0,0,1,0],
    !![1,0,0,0; 0,1,1,0; 0,0,0,1; 0,0,1,0]),
   (!![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,1],
    !![1,0,0,0; 0,1,0,0; 0,0,1,1; 0,0,1,0]),
   (!![1,0,1,0; 0,1,1,0; 0,0,1,0; 0,0,0,1],
    !![1,0,1,0; 0,1,1,0; 0,0,1,0; 0,0,0,1]),
   (!![1,0,0,1; 0,1,0,1; 0,0,0,1; 0,0,1,0],
    !![1,0,1,0; 0,1,1,0; 0,0,0,1; 0,0,1,0]),
   (!![1,0,0,1; 0,1,0,0; 0,0,0,1; 0,0,1,1],
    !![1,0,1,0; 0,1,0,0; 0,0,1,1; 0,0,1,0]),
   (!![1,0,0,0; 0,1,0,1; 0,0,0,1; 0,0,1,1],
    !![1,0,0,0; 0,1,1,0; 0,0,1,1; 0,0,1,0]),
   (!![1,0,0,1; 0,1,0,1; 0,0,0,1; 0,0,1,1],
    !![1,0,1,0; 0,1,1,0; 0,0,1,1; 0,0,1,0])]

@[expose] def kList : List (M4 × M4) :=
  [(!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]),
   (!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1],
    !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1]),
   (!![0,1,0,0; 0,0,1,0; 1,0,0,0; 0,0,0,1],
    !![0,0,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1]),
   (!![0,1,0,0; 0,0,1,0; 0,0,0,1; 1,0,0,0],
    !![0,0,0,1; 1,0,0,0; 0,1,0,0; 0,0,1,0]),
   (!![1,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1],
    !![0,1,0,0; 1,1,0,0; 0,0,1,0; 0,0,0,1]),
   (!![1,1,0,0; 0,0,1,0; 1,0,0,0; 0,0,0,1],
    !![0,0,1,0; 1,0,1,0; 0,1,0,0; 0,0,0,1]),
   (!![0,1,0,0; 1,0,1,0; 1,0,0,0; 0,0,0,1],
    !![0,0,1,0; 1,0,0,0; 0,1,1,0; 0,0,0,1]),
   (!![1,1,0,0; 0,0,1,0; 0,0,0,1; 1,0,0,0],
    !![0,0,0,1; 1,0,0,1; 0,1,0,0; 0,0,1,0]),
   (!![0,1,0,0; 1,0,1,0; 0,0,0,1; 1,0,0,0],
    !![0,0,0,1; 1,0,0,0; 0,1,0,1; 0,0,1,0]),
   (!![0,1,0,0; 0,0,1,0; 1,0,0,1; 1,0,0,0],
    !![0,0,0,1; 1,0,0,0; 0,1,0,0; 0,0,1,1]),
   (!![1,1,0,0; 1,0,1,0; 1,0,0,0; 0,0,0,1],
    !![0,0,1,0; 1,0,1,0; 0,1,1,0; 0,0,0,1]),
   (!![1,1,0,0; 1,0,1,0; 0,0,0,1; 1,0,0,0],
    !![0,0,0,1; 1,0,0,1; 0,1,0,1; 0,0,1,0]),
   (!![1,1,0,0; 0,0,1,0; 1,0,0,1; 1,0,0,0],
    !![0,0,0,1; 1,0,0,1; 0,1,0,0; 0,0,1,1]),
   (!![0,1,0,0; 1,0,1,0; 1,0,0,1; 1,0,0,0],
    !![0,0,0,1; 1,0,0,0; 0,1,0,1; 0,0,1,1]),
   (!![1,1,0,0; 1,0,1,0; 1,0,0,1; 1,0,0,0],
    !![0,0,0,1; 1,0,0,1; 0,1,0,1; 0,0,1,1])]

@[expose] def qList : List (M4 × M4) :=
  [(!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]),
   (!![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1],
    !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]),
   (!![1,0,0,0; 0,0,1,0; 0,0,0,1; 0,1,0,0],
    !![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,0]),
   (!![1,1,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,1,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]),
   (!![1,1,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1],
    !![1,0,1,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]),
   (!![1,0,0,0; 0,1,1,0; 0,1,0,0; 0,0,0,1],
    !![1,0,0,0; 0,0,1,0; 0,1,1,0; 0,0,0,1]),
   (!![1,1,0,0; 0,0,1,0; 0,0,0,1; 0,1,0,0],
    !![1,0,0,1; 0,0,0,1; 0,1,0,0; 0,0,1,0]),
   (!![1,0,0,0; 0,1,1,0; 0,0,0,1; 0,1,0,0],
    !![1,0,0,0; 0,0,0,1; 0,1,0,1; 0,0,1,0]),
   (!![1,0,0,0; 0,0,1,0; 0,1,0,1; 0,1,0,0],
    !![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,1]),
   (!![1,1,0,0; 0,1,1,0; 0,1,0,0; 0,0,0,1],
    !![1,0,1,0; 0,0,1,0; 0,1,1,0; 0,0,0,1]),
   (!![1,1,0,0; 0,1,1,0; 0,0,0,1; 0,1,0,0],
    !![1,0,0,1; 0,0,0,1; 0,1,0,1; 0,0,1,0]),
   (!![1,1,0,0; 0,0,1,0; 0,1,0,1; 0,1,0,0],
    !![1,0,0,1; 0,0,0,1; 0,1,0,0; 0,0,1,1]),
   (!![1,0,0,0; 0,1,1,0; 0,1,0,1; 0,1,0,0],
    !![1,0,0,0; 0,0,0,1; 0,1,0,1; 0,0,1,1]),
   (!![1,1,0,0; 0,1,1,0; 0,1,0,1; 0,1,0,0],
    !![1,0,0,1; 0,0,0,1; 0,1,0,1; 0,0,1,1])]

@[expose] def hTab : List (M4 × M4) :=
  [(!![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1],
    !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]),
   (!![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,0],
    !![1,0,0,0; 0,0,1,0; 0,0,0,1; 0,1,0,0]),
   (!![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,1],
    !![1,0,0,0; 0,0,1,0; 0,1,0,1; 0,1,0,0])]

theorem pList_spec : ∀ v : V4, ¬ InL0 v → ∃ pr ∈ pList, pr.1 * pr.2 = 1 ∧ InQ2 pr.1 ∧
    pr.1 *ᵥ e0 = e0 ∧ pr.1 *ᵥ v = e2 := by
  decide

theorem kList_spec : ∀ y : V4, y ≠ 0 → ∃ pr ∈ kList, pr.1 * pr.2 = 1 ∧ pr.1 *ᵥ e0 = y := by
  decide

theorem qList_spec : ∀ w : V4, w ≠ 0 → w ≠ e0 → ∃ pr ∈ qList, pr.1 * pr.2 = 1 ∧
    pr.1 *ᵥ e0 = e0 ∧ pr.1 *ᵥ e1 = w := by
  decide

abbrev allV2 : List (Fin 2 → ZMod 2) := [![0, 0], ![1, 0], ![0, 1], ![1, 1]]

theorem mem_allV2 : ∀ x : Fin 2 → ZMod 2, x ∈ allV2 := by
  decide

abbrev allB : List (Fin 2 → Fin 2 → ZMod 2) := allV2.flatMap fun r => allV2.map fun s => ![r, s]

theorem mem_allB : ∀ b : Fin 2 → Fin 2 → ZMod 2, b ∈ allB := by
  decide

abbrev FC (x : Fin 2 → ZMod 2) (b : Fin 2 → Fin 2 → ZMod 2) : Prop :=
  ∀ j : Fin 2, (b 0 j = 0 ∧ b 1 j = 0) ∨ (b 0 j = x 0 ∧ b 1 j = x 1)

abbrev fcA (x : Fin 2 → ZMod 2) : Fin 2 → Fin 2 → ZMod 2 := ![![x 0, 0], ![x 1, 0]]

abbrev fcB (x : Fin 2 → ZMod 2) : Fin 2 → Fin 2 → ZMod 2 := ![![0, x 0], ![0, x 1]]

theorem FC_list : ∀ x ∈ allV2, ∀ d ∈ allB, FC x d →
    d = 0 ∨ d = fcA x ∨ d = fcB x ∨ d = fcA x + fcB x := by
  decide

theorem FC_list' (x : Fin 2 → ZMod 2) (d : Fin 2 → Fin 2 → ZMod 2) (h : FC x d) :
    d = 0 ∨ d = fcA x ∨ d = fcB x ∨ d = fcA x + fcB x :=
  FC_list x (mem_allV2 x) d (mem_allB d) h

theorem FC_unique {x x' : Fin 2 → ZMod 2} {b : Fin 2 → Fin 2 → ZMod 2} (hb : b ≠ 0)
    (h : FC x b) (h' : FC x' b) : x = x' := by
  have hcol : ∃ j : Fin 2, ¬ (b 0 j = 0 ∧ b 1 j = 0) := by
    by_contra hcon
    push Not at hcon
    apply hb
    ext i j
    fin_cases i
    · exact (hcon j).1
    · exact (hcon j).2
  obtain ⟨j, hj⟩ := hcol
  obtain ⟨h0, h1⟩ := (h j).resolve_left hj
  obtain ⟨h0', h1'⟩ := (h' j).resolve_left hj
  ext i
  fin_cases i
  · exact h0.symm.trans h0'
  · exact h1.symm.trans h1'

abbrev NFC (b c : Fin 2 → Fin 2 → ZMod 2) : Prop :=
  b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧ ¬ ∃ x ∈ allV2, x ≠ 0 ∧ FC x b ∧ FC x c

abbrev CondST (s t : M4) : Prop :=
  s *ᵥ e0 = e0 ∧ ¬ InL0 (s *ᵥ e1) ∧ InQ2 t ∧ t *ᵥ e1 = e0 + e1

abbrev GoodTab (b c : Fin 2 → Fin 2 → ZMod 2) : Prop :=
  ∃ pr ∈ hTab, pr.1 * pr.2 = 1 ∧
    ∃ x ∈ [rBM b, rBM c, rBM (b + c)], ∃ y ∈ [rBM b, rBM c, rBM (b + c)],
      CondST (pr.1 * x * pr.2) (pr.1 * y * pr.2)

@[expose] def tabB (b c : Fin 2 → Fin 2 → ZMod 2) : Bool :=
  !decide (NFC b c) || decide (GoodTab b c)

theorem tabB_eq : ∀ b ∈ allB, ∀ c ∈ allB, tabB b c = true := by
  decide

theorem hTab_spec {b c : Fin 2 → Fin 2 → ZMod 2} (h : NFC b c) : GoodTab b c := by
  have := tabB_eq b (mem_allB b) c (mem_allB c)
  simp only [tabB, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at this
  exact this.resolve_left (not_not.mpr h)

variable {M : Type*} [CommGroup M]

@[expose] def mvec (m₀ m₁ : M) (z : V4) : M :=
  (if z 0 = 1 then m₀ else 1) * (if z 1 = 1 then m₁ else 1)

theorem ite_add_one (hM : ∀ x : M, x * x = 1) (x : M) (a b : ZMod 2) :
    (if a + b = 1 then x else 1) = (if a = 1 then x else 1) * (if b = 1 then x else 1) := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl
  · simp
  · simp
  · simp
  · have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    simp [h11, hM]

theorem mvec_add (hM : ∀ x : M, x * x = 1) (m₀ m₁ : M) (z z' : V4) :
    mvec m₀ m₁ (z + z') = mvec m₀ m₁ z * mvec m₀ m₁ z' := by
  simp only [mvec, Pi.add_apply, ite_add_one hM]
  exact mul_mul_mul_comm _ _ _ _

theorem mvec_zero (m₀ m₁ : M) : mvec m₀ m₁ 0 = 1 := by
  simp [mvec]

theorem mvec_e0 (m₀ m₁ : M) : mvec m₀ m₁ e0 = m₀ := by
  simp [mvec]

theorem mvec_e1 (m₀ m₁ : M) : mvec m₀ m₁ e1 = m₁ := by
  simp [mvec]

structure Gen (φ : SL4 →* MulAut M) (m₀ m₁ : M) : Prop where
  sq : ∀ x : M, x * x = 1
  hP : ∀ p : SL4, InQ2 (p : M4) → ∀ z : V4, InL0 z →
    φ p (mvec m₀ m₁ z) = mvec m₀ m₁ ((p : M4) *ᵥ z)
  gen : Subgroup.closure {x | ∃ g : SL4, ∃ z : V4, InL0 z ∧ φ g (mvec m₀ m₁ z) = x} = ⊤

variable {φ : SL4 →* MulAut M} {m₀ m₁ : M}

theorem Gen.fix_of_inQ2 (hG : Gen φ m₀ m₁) {p : SL4} (hp : InQ2 (p : M4))
    (hp0 : (p : M4) *ᵥ e0 = e0) : φ p m₀ = m₀ := by
  have h := hG.hP p hp e0 (by decide)
  rwa [hp0, mvec_e0] at h

theorem fix_inv {g : SL4} {x : M} (h : φ g x = x) : φ g⁻¹ x = x := by
  conv_lhs => rw [← h]
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem exists_p (v : V4) (hv : ¬ InL0 v) : ∃ p : SL4, InQ2 (p : M4) ∧ (p : M4) *ᵥ e0 = e0 ∧
    (p : M4) *ᵥ v = e2 := by
  obtain ⟨pr, -, h1, h2, h3, h4⟩ := pList_spec v hv
  exact ⟨mkSL pr.1 pr.2 h1, h2, h3, h4⟩

theorem fix_of_fix_g0 (hG : Gen φ m₀ m₁) (h0 : φ g0 m₀ = m₀) {g : SL4}
    (hg : (g : M4) *ᵥ e0 = e0) : φ g m₀ = m₀ := by
  by_cases hv : InL0 ((g : M4) *ᵥ e1)
  · have h0' : InL0 ((g : M4) *ᵥ e0) := by rw [hg]; decide
    exact hG.fix_of_inQ2 ((inQ2_iff _).2 ⟨h0', hv⟩) hg
  · obtain ⟨p, hpQ, hp0, hpv⟩ := exists_p _ hv
    set q : SL4 := g0 * p * g with hq
    have hq0 : (q : M4) *ᵥ e0 = e0 := by
      simp only [hq, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg, hp0]
      decide
    have hq1 : (q : M4) *ᵥ e1 = e1 := by
      simp only [hq, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hpv]
      decide
    have hqQ : InQ2 (q : M4) := (inQ2_iff _).2 ⟨by rw [hq0]; decide, by rw [hq1]; decide⟩
    have hqf := hG.fix_of_inQ2 hqQ hq0
    have hpf := fix_inv (hG.fix_of_inQ2 hpQ hp0)
    have hgq : g = p⁻¹ * g0 * q := by
      rw [hq, ← mul_assoc, ← mul_assoc, mul_assoc p⁻¹, g0_mul_self, mul_one, inv_mul_cancel,
        one_mul]
    rw [hgq, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hqf, h0, hpf]

theorem fix_g0_of_fix (hG : Gen φ m₀ m₁) {s : SL4} (hs0 : (s : M4) *ᵥ e0 = e0)
    (hs1 : ¬ InL0 ((s : M4) *ᵥ e1)) (hfix : φ s m₀ = m₀) : φ g0 m₀ = m₀ := by
  obtain ⟨p, hpQ, hp0, hpv⟩ := exists_p _ hs1
  set q : SL4 := g0 * p * s with hq
  have hq0 : (q : M4) *ᵥ e0 = e0 := by
    simp only [hq, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hs0, hp0]
    decide
  have hq1 : (q : M4) *ᵥ e1 = e1 := by
    simp only [hq, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hpv]
    decide
  have hqQ : InQ2 (q : M4) := (inQ2_iff _).2 ⟨by rw [hq0]; decide, by rw [hq1]; decide⟩
  have hqf := hG.fix_of_inQ2 hqQ hq0
  have hpf := fix_inv (hG.fix_of_inQ2 hpQ hp0)
  have hsf := fix_inv hfix
  have hg0 : g0 = q * s⁻¹ * p⁻¹ := by
    rw [hq]
    group
  rw [hg0, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hpf, hsf, hqf]

theorem fix_of_quad (hG : Gen φ m₀ m₁) {s t : SL4} (hst : CondST (s : M4) (t : M4))
    (hq : ∀ v : M, φ s (φ t v * v⁻¹) = φ t v * v⁻¹) : φ g0 m₀ = m₀ := by
  obtain ⟨hs0, hs1, htQ, ht1⟩ := hst
  have h1 : φ t m₁ = m₀ * m₁ := by
    have := hG.hP t htQ e1 (by decide)
    rwa [mvec_e1, ht1, mvec_add hG.sq, mvec_e0, mvec_e1] at this
  have h2 : φ t m₁ * m₁⁻¹ = m₀ := by rw [h1, mul_inv_cancel_right]
  have h3 := hq m₁
  rw [h2] at h3
  exact fix_g0_of_fix hG hs0 hs1 h3

@[expose] def QuadHyp (φ : SL4 →* MulAut M) (S : Subgroup SL4) : Prop :=
  ∀ h : SL4, ∀ a ∈ S, ∀ a' ∈ S, ∀ v : M,
    φ (h * a * h⁻¹) (φ (h * a' * h⁻¹) v * v⁻¹) = φ (h * a' * h⁻¹) v * v⁻¹

theorem conj_mkSL {m n : M4} (h : m * n = 1) {x : SL4} :
    mkSL m n h * x * (mkSL m n h)⁻¹ =
      mkSL (m * (x : M4) * n) (m * ((x⁻¹ : SL4) : M4) * n) (by
        rw [show m * (x : M4) * n * (m * ((x⁻¹ : SL4) : M4) * n) =
          m * ((x : M4) * (n * m) * ((x⁻¹ : SL4) : M4)) * n by noncomm_ring,
          mul_eq_one_comm.mp h, mul_one, ← Matrix.SpecialLinearGroup.coe_mul,
          mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, mul_one, h]) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_mkSL_inv]
  rfl

theorem fix_of_nfc (hG : Gen φ m₀ m₁) {S : Subgroup SL4} (hq : QuadHyp φ S)
    {b c : Fin 2 → Fin 2 → ZMod 2} (hb : rB b ∈ S) (hc : rB c ∈ S) (hbc : NFC b c) :
    φ g0 m₀ = m₀ := by
  obtain ⟨pr, -, hpr, x, hx, y, hy, hxy⟩ := hTab_spec hbc
  have hbcS : rB (b + c) ∈ S := by rw [rB_add]; exact S.mul_mem hb hc
  have hmem : ∀ z ∈ [rBM b, rBM c, rBM (b + c)], ∃ a ∈ S, (a : M4) = z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨rB b, hb, rfl⟩
    · exact ⟨rB c, hc, rfl⟩
    · exact ⟨rB (b + c), hbcS, rfl⟩
  obtain ⟨a, haS, rfl⟩ := hmem x hx
  obtain ⟨a', ha'S, rfl⟩ := hmem y hy
  set h := mkSL pr.1 pr.2 hpr
  refine fix_of_quad hG (s := h * a * h⁻¹) (t := h * a' * h⁻¹) ?_ (hq h a haS a' ha'S)
  rw [conj_mkSL hpr, conj_mkSL hpr, coe_mkSL, coe_mkSL]
  exact hxy

@[expose] def s01 : SL4 := mkSL s01M s01M (by decide)

@[expose] def t01 : SL4 := mkSL t01M t01M (by decide)

theorem exists_e0 {y : V4} (hy : y ≠ 0) : ∃ g : SL4, (g : M4) *ᵥ e0 = y := by
  obtain ⟨pr, -, h1, h2⟩ := kList_spec y hy
  exact ⟨mkSL pr.1 pr.2 h1, h2⟩

@[expose] noncomputable def psi (φ : SL4 →* MulAut M) (m₀ : M) (y : V4) : M :=
  if hy : y = 0 then 1 else φ (Classical.choose (exists_e0 hy)) m₀

theorem psi_zero (φ : SL4 →* MulAut M) (m₀ : M) : psi φ m₀ 0 = 1 := by
  simp [psi]

theorem psi_eq (hG : Gen φ m₀ m₁) (h0 : φ g0 m₀ = m₀) {y : V4} (hy : y ≠ 0) {g : SL4}
    (hg : (g : M4) *ᵥ e0 = y) : psi φ m₀ y = φ g m₀ := by
  simp only [psi, hy, ↓reduceDIte]
  set g' := Classical.choose (exists_e0 hy) with hg'def
  have hg' : (g' : M4) *ᵥ e0 = y := Classical.choose_spec (exists_e0 hy)
  have hk : ((g'⁻¹ * g : SL4) : M4) *ᵥ e0 = e0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg, ← hg', inv_mulVec_mulVec]
  have hfix := fix_of_fix_g0 hG h0 hk
  rw [show g = g' * (g'⁻¹ * g) by group, map_mul, MulAut.mul_apply, hfix]

theorem psi_smul (hG : Gen φ m₀ m₁) (h0 : φ g0 m₀ = m₀) (g : SL4) (y : V4) :
    psi φ m₀ ((g : M4) *ᵥ y) = φ g (psi φ m₀ y) := by
  by_cases hy : y = 0
  · rw [hy, mulVec_zero, psi_zero, map_one]
  · have hgy : (g : M4) *ᵥ y ≠ 0 := by
      intro h
      apply hy
      rw [← inv_mulVec_mulVec g y, h, mulVec_zero]
    obtain ⟨g', hg'⟩ := exists_e0 hy
    rw [psi_eq hG h0 hy hg', psi_eq hG h0 hgy (g := g * g')
      (by rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg']), map_mul,
      MulAut.mul_apply]

theorem psi_L0 (hG : Gen φ m₀ m₁) (h0 : φ g0 m₀ = m₀) {z : V4} (hz : InL0 z) :
    psi φ m₀ z = mvec m₀ m₁ z := by
  rcases inL0_cases z hz with rfl | rfl | rfl | rfl
  · rw [psi_zero, mvec_zero]
  · rw [psi_eq hG h0 (by decide) (g := 1) (by simp), map_one, MulAut.one_apply, mvec_e0]
  · rw [psi_eq hG h0 (by decide) (g := s01) (by decide)]
    have := hG.hP s01 (by decide) e0 (by decide)
    rwa [mvec_e0, show ((s01 : SL4) : M4) *ᵥ e0 = e1 by decide] at this
  · rw [psi_eq hG h0 (by decide) (g := t01) (by decide)]
    have := hG.hP t01 (by decide) e0 (by decide)
    rwa [mvec_e0, show ((t01 : SL4) : M4) *ᵥ e0 = e0 + e1 by decide] at this

theorem add_self_V4 : ∀ y : V4, y + y = 0 := by
  decide

theorem psi_add (hG : Gen φ m₀ m₁) (h0 : φ g0 m₀ = m₀) (y y' : V4) :
    psi φ m₀ (y + y') = psi φ m₀ y * psi φ m₀ y' := by
  by_cases hy : y = 0
  · rw [hy, zero_add, psi_zero, one_mul]
  by_cases hy' : y' = 0
  · rw [hy', add_zero, psi_zero, mul_one]
  by_cases hyy : y = y'
  · rw [← hyy, add_self_V4, psi_zero, hG.sq]
  obtain ⟨g', hg'⟩ := exists_e0 hy
  set w := ((g'⁻¹ : SL4) : M4) *ᵥ y' with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hy'
    rw [← mulVec_inv_mulVec g' y', ← hw, h, mulVec_zero]
  have hwe : w ≠ e0 := by
    intro h
    apply hyy
    rw [← hg', ← h, hw, mulVec_inv_mulVec]
  obtain ⟨pr, -, h1, hq0, hq1⟩ := qList_spec w hw0 hwe
  set g := g' * mkSL pr.1 pr.2 h1 with hgdef
  have hge0 : (g : M4) *ᵥ e0 = y := by
    rw [hgdef, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, coe_mkSL, hq0, hg']
  have hge1 : (g : M4) *ᵥ e1 = y' := by
    rw [hgdef, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, coe_mkSL, hq1, hw,
      mulVec_inv_mulVec]
  rw [← hge0, ← hge1, ← mulVec_add, psi_smul hG h0, psi_smul hG h0, psi_smul hG h0,
    psi_L0 hG h0 (by decide), psi_L0 hG h0 (by decide), psi_L0 hG h0 (by decide),
    mvec_add hG.sq, mvec_e0, mvec_e1, map_mul]

theorem injective_of_fix (hG : Gen φ m₀ m₁) (h0 : φ g0 m₀ = m₀) (β : M →* Multiplicative V4)
    (hβ : ∀ g v, Multiplicative.toAdd (β (φ g v)) = (g : M4) *ᵥ Multiplicative.toAdd (β v))
    (hβ0 : Multiplicative.toAdd (β m₀) = e0) (hβ1 : Multiplicative.toAdd (β m₁) = e1) :
    Function.Injective β := by
  have hβm : ∀ z, InL0 z → Multiplicative.toAdd (β (mvec m₀ m₁ z)) = z := by
    intro z hz
    rcases inL0_cases z hz with rfl | rfl | rfl | rfl
    · rw [mvec_zero, map_one]; rfl
    · rw [mvec_e0, hβ0]
    · rw [mvec_e1, hβ1]
    · rw [mvec_add hG.sq, mvec_e0, mvec_e1, map_mul, toAdd_mul, hβ0, hβ1]
  set K : Subgroup M :=
    { carrier := {x | psi φ m₀ (Multiplicative.toAdd (β x)) = x}
      mul_mem' := by
        intro x x' hx hx'
        simp only [Set.mem_ofPred_eq] at hx hx' ⊢
        rw [map_mul, toAdd_mul, psi_add hG h0, hx, hx']
      one_mem' := by
        simp only [Set.mem_ofPred_eq, map_one, toAdd_one, psi_zero]
      inv_mem' := by
        intro x hx
        have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hG.sq x)
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [hinv]
        exact hx } with hK
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← hG.gen, Subgroup.closure_le]
    rintro x ⟨g, z, hz, rfl⟩
    show psi φ m₀ (Multiplicative.toAdd (β (φ g (mvec m₀ m₁ z)))) = φ g (mvec m₀ m₁ z)
    rw [hβ, hβm z hz, psi_smul hG h0, psi_L0 hG h0 hz]
  have key : ∀ x, psi φ m₀ (Multiplicative.toAdd (β x)) = x := fun x => by
    have : x ∈ K := hKtop ▸ Subgroup.mem_top x
    exact this
  intro x x' h
  rw [← key x, ← key x', h]

theorem nfc_or_fc {S : Subgroup SL4} (hSR : ∀ y ∈ S, ∃ b, y = rB b) (h4 : 4 ≤ Nat.card S) :
    (∃ b c, rB b ∈ S ∧ rB c ∈ S ∧ NFC b c) ∨
      ∃ x : Fin 2 → ZMod 2, x ≠ 0 ∧ rB (fcA x) ∈ S ∧ rB (fcB x) ∈ S ∧
        ∀ y ∈ S, y = 1 ∨ y = rB (fcA x) ∨ y = rB (fcB x) ∨ y = rB (fcA x + fcB x) := by
  classical
  by_cases hN : ∃ b c, rB b ∈ S ∧ rB c ∈ S ∧ NFC b c
  · exact Or.inl hN
  right
  have hN' : ∀ b c, rB b ∈ S → rB c ∈ S → b ≠ 0 → c ≠ 0 → b ≠ c →
      ∃ x ∈ allV2, x ≠ 0 ∧ FC x b ∧ FC x c := by
    intro b c hb hc hb0 hc0 hbc
    by_contra hcon
    exact hN ⟨b, c, hb, hc, hb0, hc0, hbc, hcon⟩
  set T := Finset.univ.filter (fun b : Fin 2 → Fin 2 → ZMod 2 => rB b ∈ S) with hT
  have hcard : Nat.card S = T.card := by
    rw [hT, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.ofBijective (fun b => ⟨rB b.1, b.2⟩) ⟨?_, ?_⟩).symm
    · intro b c h
      exact Subtype.ext (rB_injective (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := hSR y hy
      exact ⟨⟨b, hy⟩, rfl⟩
  have h3 : 2 < T.card := by omega
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ := Finset.two_lt_card.1 h3
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv hw
  obtain ⟨b₁, c₁, hb₁, hc₁, hb₁0, hc₁0, hbc⟩ : ∃ b c, rB b ∈ S ∧ rB c ∈ S ∧ b ≠ 0 ∧ c ≠ 0 ∧
      b ≠ c := by
    by_cases hu0 : u = 0
    · exact ⟨v, w, hv, hw, fun h => huv (hu0.trans h.symm), fun h => huw (hu0.trans h.symm),
        hvw⟩
    · by_cases hv0 : v = 0
      · exact ⟨u, w, hu, hw, hu0, fun h => hvw (hv0.trans h.symm), huw⟩
      · exact ⟨u, v, hu, hv, hu0, hv0, huv⟩
  obtain ⟨x, -, hx0, hxb, hxc⟩ := hN' b₁ c₁ hb₁ hc₁ hb₁0 hc₁0 hbc
  have hall : ∀ b, rB b ∈ S → FC x b := by
    intro b hb
    by_cases hb0 : b = 0
    · rw [hb0]
      intro j
      exact Or.inl ⟨rfl, rfl⟩
    by_cases hbb : b₁ = b
    · exact hbb ▸ hxb
    obtain ⟨x', -, -, hx'b₁, hx'b⟩ := hN' b₁ b hb₁ hb hb₁0 hb0 hbb
    rw [FC_unique hb₁0 hxb hx'b₁]
    exact hx'b
  have hsub : ∀ y ∈ S, y = 1 ∨ y = rB (fcA x) ∨ y = rB (fcB x) ∨ y = rB (fcA x + fcB x) := by
    intro y hy
    obtain ⟨b, rfl⟩ := hSR y hy
    rcases FC_list' x b (hall b hy) with h | h | h | h
    · left; rw [h, rB_zero]
    · right; left; rw [h]
    · right; right; left; rw [h]
    · right; right; right; rw [h]
  set F : Finset SL4 := {1, rB (fcA x), rB (fcB x), rB (fcA x + fcB x)} with hF
  have hsubF : (S : Set SL4) ⊆ ↑F := by
    intro y hy
    rcases hsub y hy with h | h | h | h <;> simp [hF, h]
  have hFc : F.card ≤ 4 := Finset.card_le_four
  have hSc : (S : Set SL4).ncard = Nat.card S := (Nat.card_coe_set_eq _).symm
  have heq : (S : Set SL4) = ↑F :=
    Set.eq_of_subset_of_ncard_le hsubF (by rw [Set.ncard_coe_finset, hSc]; omega)
  have hA : rB (fcA x) ∈ S := by
    have : rB (fcA x) ∈ (↑F : Set SL4) := by simp [hF]
    rw [← heq] at this
    exact this
  have hB : rB (fcB x) ∈ S := by
    have : rB (fcB x) ∈ (↑F : Set SL4) := by simp [hF]
    rw [← heq] at this
    exact this
  exact ⟨x, hx0, hA, hB, hsub⟩

end CFSG.Quasithin.H13.A6.L4Ind
