module

public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.LieType.Chevalley.C2E6StandardFixedData

public noncomputable section

namespace CFSG.RankThree.E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std Matrix
open scoped commutatorElement Pointwise

@[expose] def a3Weight : Fin 4 → Fin Tag.E6.rank → ℤ :=
  (![![1, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 1, 0]] :
    Fin 4 → Fin 6 → ℤ)

theorem exists_e6RootVec_a3Weight : ∀ k : Fin 4, ∃ m : Fin 72, e6RootVec m = a3Weight k := by
  decide +kernel

theorem isRoot_a3Weight (k : Fin 4) : IsRoot Tag.E6 (a3Weight k) := by
  obtain ⟨m, hm⟩ := exists_e6RootVec_a3Weight k
  rw [← hm]
  exact isRoot_e6RootVec m

theorem a3Weight_injective : Function.Injective a3Weight := by
  intro k k' h
  revert k k'
  decide

abbrev a3Label (k : Fin 4) : Label Tag.E6 := Sum.inr ⟨a3Weight k, isRoot_a3Weight k⟩

theorem a3Label_injective : Function.Injective a3Label := by
  intro k k' h
  exact a3Weight_injective (congrArg Subtype.val (Sum.inr_injective h))

variable (K : Type) [Field K]

@[expose] def a3Vec (k : Fin 4) : RootModule Tag.E6 K := Finsupp.single (a3Label k) 1

theorem rootVec_a3Weight (k : Fin 4) : rootVec Tag.E6 K (a3Weight k) = a3Vec K k :=
  C2E6Std.rootVec_eq_single (isRoot_a3Weight k)

variable {K}

theorem a3Vec_apply (k i : Fin 4) : a3Vec K k (a3Label i) = if i = k then 1 else 0 := by
  rw [a3Vec, Finsupp.single_apply]
  by_cases h : i = k
  · rw [ite_eq_left (congrArg a3Label h).symm, ite_eq_left h]
  · rw [ite_eq_right fun e => h (a3Label_injective e).symm, ite_eq_right h]

theorem rootVec_apply_a3Label (γ : Fin Tag.E6.rank → ℤ) (i : Fin 4) :
    rootVec Tag.E6 K γ (a3Label i) = if γ = a3Weight i then 1 else 0 := by
  by_cases hγ : IsRoot Tag.E6 γ
  · rw [C2E6Std.rootVec_eq_single hγ, Finsupp.single_apply]
    by_cases h : γ = a3Weight i
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [C2E6Std.rootVec_eq_zero_of_not hγ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hγ (isRoot_a3Weight i)

variable (K) in
@[expose] def a3Module : Submodule K (RootModule Tag.E6 K) :=
  Submodule.span K (Set.range (a3Vec K))

theorem a3Vec_mem (k : Fin 4) : a3Vec K k ∈ a3Module K :=
  Submodule.subset_span ⟨k, rfl⟩

theorem eq_sum_of_mem_a3Module {m : RootModule Tag.E6 K} (hm : m ∈ a3Module K) :
    m = ∑ k, m (a3Label k) • a3Vec K k := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [a3Vec_apply, ite_eq_right hj, zero_smul])
      (by simp), a3Vec_apply, ite_eq_left rfl, one_smul]
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finsupp.add_apply, add_smul]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, mul_smul]

theorem rootVec_mem_a3Module {γ : Fin Tag.E6.rank → ℤ}
    (h : (∀ m : Fin 72, e6RootVec m ≠ γ) ∨ ∃ k, a3Weight k = γ) :
    rootVec Tag.E6 K γ ∈ a3Module K := by
  rcases h with h | ⟨k, rfl⟩
  · have hγ : ¬IsRoot Tag.E6 γ := fun hγ => by
      obtain ⟨m, hm⟩ := isRoot_iff_exists_e6RootVec.1 hγ
      exact h m hm
    rw [C2E6Std.rootVec_eq_zero_of_not hγ]
    exact zero_mem _
  · rw [rootVec_a3Weight]
    exact a3Vec_mem k

theorem a3Weight_ne_single : ∀ k : Fin 4, ∀ i : Fin 6, (i = 0 ∨ i = 2 ∨ i = 3) →
    a3Weight k ≠ Pi.single (e6Index i) 1 ∧ a3Weight k ≠ -Pi.single (e6Index i) 1 := by
  decide +kernel

theorem a3Weight_add_single : ∀ k : Fin 4, ∀ i : Fin 6, (i = 0 ∨ i = 2 ∨ i = 3) →
    (∀ m : Fin 72, e6RootVec m ≠ a3Weight k + Pi.single (e6Index i) 1) ∨
      ∃ k', a3Weight k' = a3Weight k + Pi.single (e6Index i) 1 := by
  decide +kernel

theorem a3Weight_sub_single : ∀ k : Fin 4, ∀ i : Fin 6, (i = 0 ∨ i = 2 ∨ i = 3) →
    (∀ m : Fin 72, e6RootVec m ≠ a3Weight k - Pi.single (e6Index i) 1) ∨
      ∃ k', a3Weight k' = a3Weight k - Pi.single (e6Index i) 1 := by
  decide +kernel

theorem xOp_a3Vec {i : Fin Tag.E6.rank} (hi : i ∈ support134) (c : K) (k : Fin 4) :
    xOp Tag.E6 K i c (a3Vec K k) =
      a3Vec K k + c • rootVec Tag.E6 K (a3Weight k + Pi.single i 1) := by
  rw [← rootVec_a3Weight]
  exact xOp_rootVec_E6 i c (isRoot_a3Weight k) (a3Weight_ne_single k i ((mem_support134 i).1 hi)).1
    (a3Weight_ne_single k i ((mem_support134 i).1 hi)).2

theorem yOp_a3Vec {i : Fin Tag.E6.rank} (hi : i ∈ support134) (c : K) (k : Fin 4) :
    yOp Tag.E6 K i c (a3Vec K k) =
      a3Vec K k + c • rootVec Tag.E6 K (a3Weight k - Pi.single i 1) := by
  rw [← rootVec_a3Weight]
  exact yOp_rootVec_E6 i c (isRoot_a3Weight k) (a3Weight_ne_single k i ((mem_support134 i).1 hi)).1
    (a3Weight_ne_single k i ((mem_support134 i).1 hi)).2

theorem mem_a3Module_of_mem {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support134)
    {m : RootModule Tag.E6 K} (hm : m ∈ a3Module K) :
    (g : Module.End K (RootModule Tag.E6 K)) m ∈ a3Module K := by
  refine mem_of_mem_subsystemGroup (fun i hi c v hv => ?_) (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [xOp_a3Vec hi]
      exact add_mem (a3Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_a3Module (a3Weight_add_single k i ((mem_support134 i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [yOp_a3Vec hi]
      exact add_mem (a3Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_a3Module (a3Weight_sub_single k i ((mem_support134 i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

@[expose] def a3Mat (g : ModGL Tag.E6 K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => (g : Module.End K (RootModule Tag.E6 K)) (a3Vec K j) (a3Label i)

theorem apply_a3Vec {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support134)
    (j : Fin 4) :
    (g : Module.End K (RootModule Tag.E6 K)) (a3Vec K j) = ∑ i, a3Mat g i j • a3Vec K i :=
  eq_sum_of_mem_a3Module (mem_a3Module_of_mem hg (a3Vec_mem j))

theorem a3Mat_one : a3Mat (1 : ModGL Tag.E6 K) = 1 := by
  ext i j
  rw [a3Mat, Matrix.of_apply, Units.val_one, Module.End.one_apply, a3Vec_apply, Matrix.one_apply]

theorem a3Mat_mul {g h : ModGL Tag.E6 K} (_hg : g ∈ subsystemGroup Tag.E6 K support134)
    (hh : h ∈ subsystemGroup Tag.E6 K support134) :
    a3Mat (g * h) = a3Mat g * a3Mat h := by
  ext i j
  rw [a3Mat, Matrix.of_apply, Units.val_mul, Module.End.mul_apply, apply_a3Vec hh, map_sum,
    Finsupp.finsetSum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem a3Mat_xUnit {i₀ : Fin 6} (hi : e6Index i₀ ∈ support134) {p q : Fin 4}
    (hpq : ∀ i j : Fin 4, a3Weight j + Pi.single (e6Index i₀) 1 = a3Weight i ↔ (i = p ∧ j = q))
    (t : K) : a3Mat (xUnit Tag.E6 K (e6Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [a3Mat, Matrix.of_apply, coe_xUnit, xOp_a3Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_a3Label, a3Vec_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have key := hpq i j
  by_cases h : a3Weight j + Pi.single (e6Index i₀) 1 = a3Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem a3Mat_yUnit {i₀ : Fin 6} (hi : e6Index i₀ ∈ support134) {p q : Fin 4}
    (hpq : ∀ i j : Fin 4, a3Weight j - Pi.single (e6Index i₀) 1 = a3Weight i ↔ (i = p ∧ j = q))
    (t : K) : a3Mat (yUnit Tag.E6 K (e6Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [a3Mat, Matrix.of_apply, coe_yUnit, yOp_a3Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_a3Label, a3Vec_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have key := hpq i j
  by_cases h : a3Weight j - Pi.single (e6Index i₀) 1 = a3Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem mem_support134_0 : e6Index 0 ∈ support134 := (mem_support134 _).2 (Or.inl rfl)
theorem mem_support134_2 : e6Index 2 ∈ support134 := (mem_support134 _).2 (Or.inr (Or.inl rfl))
theorem mem_support134_3 : e6Index 3 ∈ support134 := (mem_support134 _).2 (Or.inr (Or.inr rfl))

theorem a3Mat_x1 (t : K) : a3Mat (xUnit Tag.E6 K (e6Index 0) t) = 1 + single 0 1 t :=
  a3Mat_xUnit mem_support134_0 (by decide +kernel) t

theorem a3Mat_y1 (t : K) : a3Mat (yUnit Tag.E6 K (e6Index 0) t) = 1 + single 1 0 t :=
  a3Mat_yUnit mem_support134_0 (by decide +kernel) t

theorem a3Mat_x3 (t : K) : a3Mat (xUnit Tag.E6 K (e6Index 2) t) = 1 + single 1 2 t :=
  a3Mat_xUnit mem_support134_2 (by decide +kernel) t

theorem a3Mat_y3 (t : K) : a3Mat (yUnit Tag.E6 K (e6Index 2) t) = 1 + single 2 1 t :=
  a3Mat_yUnit mem_support134_2 (by decide +kernel) t

theorem a3Mat_x4 (t : K) : a3Mat (xUnit Tag.E6 K (e6Index 3) t) = 1 + single 2 3 t :=
  a3Mat_xUnit mem_support134_3 (by decide +kernel) t

theorem a3Mat_y4 (t : K) : a3Mat (yUnit Tag.E6 K (e6Index 3) t) = 1 + single 3 2 t :=
  a3Mat_yUnit mem_support134_3 (by decide +kernel) t

theorem a3Weight_pairing : ∀ k : Fin 4,
    (∑ j, Tag.E6.cartan (e6Index 0) j * a3Weight k j) = (![1, -1, 0, 0] : Fin 4 → ℤ) k ∧
    (∑ j, Tag.E6.cartan (e6Index 2) j * a3Weight k j) = (![0, 1, -1, 0] : Fin 4 → ℤ) k ∧
    (∑ j, Tag.E6.cartan (e6Index 3) j * a3Weight k j) = (![0, 0, 1, -1] : Fin 4 → ℤ) k := by
  decide +kernel

theorem a3Mat_torusElt (i : Fin Tag.E6.rank) (a : Kˣ) :
    a3Mat (torusElt Tag.E6 K i a) = Matrix.diagonal fun k =>
      ((a ^ (∑ j, Tag.E6.cartan i j * a3Weight k j) : Kˣ) : K) := by
  ext p q
  rw [a3Mat, Matrix.of_apply, ← rootVec_a3Weight, torusElt_rootVec i a (isRoot_a3Weight q),
    rootVec_a3Weight, Finsupp.smul_apply, a3Vec_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

theorem torusElt_mem_a3Group {i : Fin Tag.E6.rank} (hi : i ∈ support134) (a : Kˣ) :
    torusElt Tag.E6 K i a ∈ subsystemGroup Tag.E6 K support134 :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

@[expose] def a3TorusElt (a b c : Kˣ) : ModGL Tag.E6 K :=
  torusElt Tag.E6 K (e6Index 0) a * torusElt Tag.E6 K (e6Index 2) b *
    torusElt Tag.E6 K (e6Index 3) c

theorem a3TorusElt_mem (a b c : Kˣ) : a3TorusElt a b c ∈ subsystemGroup Tag.E6 K support134 :=
  mul_mem (mul_mem (torusElt_mem_a3Group mem_support134_0 a)
    (torusElt_mem_a3Group mem_support134_2 b)) (torusElt_mem_a3Group mem_support134_3 c)

theorem a3Mat_a3TorusElt (a b c : Kˣ) :
    a3Mat (a3TorusElt a b c) =
      Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ * c : Kˣ) : K), ((c⁻¹ : Kˣ) : K)] := by
  rw [a3TorusElt, a3Mat_mul (mul_mem (torusElt_mem_a3Group mem_support134_0 a)
      (torusElt_mem_a3Group mem_support134_2 b)) (torusElt_mem_a3Group mem_support134_3 c),
    a3Mat_mul (torusElt_mem_a3Group mem_support134_0 a) (torusElt_mem_a3Group mem_support134_2 b),
    a3Mat_torusElt, a3Mat_torusElt, a3Mat_torusElt, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  obtain ⟨h0, h2, h3⟩ := a3Weight_pairing k
  rw [h0, h2, h3]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg]

theorem det_a3Mat {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support134) :
    (a3Mat g).det = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_support134 i).1 hi with rfl | rfl | rfl
      · rw [a3Mat_x1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [a3Mat_x3]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [a3Mat_x4]; exact det_transvection_of_ne _ _ (by decide) _
    · rcases (mem_support134 i).1 hi with rfl | rfl | rfl
      · rw [a3Mat_y1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [a3Mat_y3]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [a3Mat_y4]; exact det_transvection_of_ne _ _ (by decide) _
  | one => rw [a3Mat_one, det_one]
  | mul x y hx hy ihx ihy => rw [a3Mat_mul hx hy, det_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have h := a3Mat_mul (inv_mem hx) hx
    rw [inv_mul_cancel, a3Mat_one] at h
    have h' := congrArg Matrix.det h
    rw [det_one, det_mul, ih, mul_one] at h'
    exact h'.symm

variable (K) in
@[expose] def a3Rep : subsystemGroup Tag.E6 K support134 →* SpecialLinearGroup (Fin 4) K where
  toFun g := ⟨a3Mat (g : ModGL Tag.E6 K), det_a3Mat g.2⟩
  map_one' := Subtype.ext a3Mat_one
  map_mul' g h := Subtype.ext (a3Mat_mul g.2 h.2)

theorem coe_a3Rep (g : subsystemGroup Tag.E6 K support134) :
    ((a3Rep K g : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      a3Mat (g : ModGL Tag.E6 K) :=
  rfl

theorem a3Mat_inv {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support134) :
    a3Mat g⁻¹ = (a3Mat g)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← a3Mat_mul hg (inv_mem hg), mul_inv_cancel, a3Mat_one]

theorem pinnedX_mem_a3Group {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 support134) (t : K) :
    pinnedX Tag.E6 K α t ∈ subsystemGroup Tag.E6 K support134 :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def A3RootFamily (i j : Fin 4) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
    a3Mat (pinnedX Tag.E6 K (chainRoot chain134 i j) t) = 1 + single i j ((ε : K) * t)

theorem a3RootFamily_of_eq {i j : Fin 4} {g : K → ModGL Tag.E6 K}
    (hg : ∀ t, pinnedX Tag.E6 K (chainRoot chain134 i j) t = g t)
    (h : ∀ t, a3Mat (g t) = 1 + single i j t) : A3RootFamily K i j :=
  ⟨1, Or.inl rfl, fun t => by rw [hg, h, Int.cast_one, one_mul]⟩

theorem a3RootFamily_comp {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsum : chainRoot chain134 i j + chainRoot chain134 j k = chainRoot chain134 i k)
    (hne : chainRoot chain134 i j ≠ chainRoot chain134 j k)
    (hne' : chainRoot chain134 i j ≠ -chainRoot chain134 j k)
    (h₁ : A3RootFamily K i j) (h₂ : A3RootFamily K j k) : A3RootFamily K i k := by
  obtain ⟨ε₁, hε₁, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, h₂⟩ := h₂
  have hα := chainRoot134_mem_parabolicRoots hij
  have hβ := chainRoot134_mem_parabolicRoots hjk
  have hγ := chainRoot134_mem_parabolicRoots hik
  obtain ⟨hC, hcomm⟩ := (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) hα.1
    hβ.1 hne hne').1 (hsum ▸ hγ.1)
  set C := commConst Tag.E6 (chainRoot chain134 i j) (chainRoot chain134 j k) (1, 1)
  have hCC : (C : K) * C = 1 := by rcases hC with h | h <;> rw [h] <;> norm_num
  refine ⟨ε₁ * ε₂ * C, ?_, fun t => ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> rcases hC with h | h <;>
      simp [h]
  have e : pinnedX Tag.E6 K (chainRoot chain134 i k) t =
      ⁅pinnedX Tag.E6 K (chainRoot chain134 i j) 1,
        pinnedX Tag.E6 K (chainRoot chain134 j k) ((C : K) * t)⁆ := by
    rw [hcomm K 1 ((C : K) * t), hsum]
    congr 1
    rw [mul_one, ← mul_assoc, hCC, one_mul]
  have m1 := pinnedX_mem_a3Group hα (1 : K)
  have m2 := pinnedX_mem_a3Group hβ ((C : K) * t)
  rw [e, commutatorElement_def, a3Mat_mul (mul_mem (mul_mem m1 m2) (inv_mem m1)) (inv_mem m2),
    a3Mat_mul (mul_mem m1 m2) (inv_mem m1), a3Mat_mul m1 m2, a3Mat_inv m1, a3Mat_inv m2, h₁, h₂,
    CFSG.LinearGroups.elementary_three_index_commutator hik hij hjk.symm]
  congr 2
  push_cast
  ring

theorem chainRoot134_values :
    chainRoot chain134 0 1 = Pi.single (e6Index 0) 1 ∧
    chainRoot chain134 1 2 = Pi.single (e6Index 2) 1 ∧
    chainRoot chain134 2 3 = Pi.single (e6Index 3) 1 ∧
    chainRoot chain134 1 0 = -Pi.single (e6Index 0) 1 ∧
    chainRoot chain134 2 1 = -Pi.single (e6Index 2) 1 ∧
    chainRoot chain134 3 2 = -Pi.single (e6Index 3) 1 := by
  decide +kernel

theorem chainRoot134_sums :
    (chainRoot chain134 0 1 + chainRoot chain134 1 2 = chainRoot chain134 0 2 ∧
      chainRoot chain134 0 1 ≠ chainRoot chain134 1 2 ∧
      chainRoot chain134 0 1 ≠ -chainRoot chain134 1 2) ∧
    (chainRoot chain134 1 2 + chainRoot chain134 2 3 = chainRoot chain134 1 3 ∧
      chainRoot chain134 1 2 ≠ chainRoot chain134 2 3 ∧
      chainRoot chain134 1 2 ≠ -chainRoot chain134 2 3) ∧
    (chainRoot chain134 0 2 + chainRoot chain134 2 3 = chainRoot chain134 0 3 ∧
      chainRoot chain134 0 2 ≠ chainRoot chain134 2 3 ∧
      chainRoot chain134 0 2 ≠ -chainRoot chain134 2 3) ∧
    (chainRoot chain134 2 1 + chainRoot chain134 1 0 = chainRoot chain134 2 0 ∧
      chainRoot chain134 2 1 ≠ chainRoot chain134 1 0 ∧
      chainRoot chain134 2 1 ≠ -chainRoot chain134 1 0) ∧
    (chainRoot chain134 3 2 + chainRoot chain134 2 1 = chainRoot chain134 3 1 ∧
      chainRoot chain134 3 2 ≠ chainRoot chain134 2 1 ∧
      chainRoot chain134 3 2 ≠ -chainRoot chain134 2 1) ∧
    (chainRoot chain134 3 2 + chainRoot chain134 2 0 = chainRoot chain134 3 0 ∧
      chainRoot chain134 3 2 ≠ chainRoot chain134 2 0 ∧
      chainRoot chain134 3 2 ≠ -chainRoot chain134 2 0) := by
  decide +kernel

theorem a3RootFamily_all : ∀ i j : Fin 4, i ≠ j → A3RootFamily K i j := by
  obtain ⟨c01, c12, c23, c10, c21, c32⟩ := chainRoot134_values
  obtain ⟨s02, s13, s03, s20, s31, s30⟩ := chainRoot134_sums
  have f01 : A3RootFamily K 0 1 := a3RootFamily_of_eq (fun t => by rw [c01, pinnedX_single])
    a3Mat_x1
  have f12 : A3RootFamily K 1 2 := a3RootFamily_of_eq (fun t => by rw [c12, pinnedX_single])
    a3Mat_x3
  have f23 : A3RootFamily K 2 3 := a3RootFamily_of_eq (fun t => by rw [c23, pinnedX_single])
    a3Mat_x4
  have f10 : A3RootFamily K 1 0 := a3RootFamily_of_eq
    (fun t => by rw [c10, pinnedX_neg_single]) a3Mat_y1
  have f21 : A3RootFamily K 2 1 := a3RootFamily_of_eq
    (fun t => by rw [c21, pinnedX_neg_single]) a3Mat_y3
  have f32 : A3RootFamily K 3 2 := a3RootFamily_of_eq
    (fun t => by rw [c32, pinnedX_neg_single]) a3Mat_y4
  have f02 := a3RootFamily_comp (by decide) (by decide) (by decide) s02.1 s02.2.1 s02.2.2 f01 f12
  have f13 := a3RootFamily_comp (by decide) (by decide) (by decide) s13.1 s13.2.1 s13.2.2 f12 f23
  have f03 := a3RootFamily_comp (by decide) (by decide) (by decide) s03.1 s03.2.1 s03.2.2 f02 f23
  have f20 := a3RootFamily_comp (by decide) (by decide) (by decide) s20.1 s20.2.1 s20.2.2 f21 f10
  have f31 := a3RootFamily_comp (by decide) (by decide) (by decide) s31.1 s31.2.1 s31.2.2 f32 f21
  have f30 := a3RootFamily_comp (by decide) (by decide) (by decide) s30.1 s30.2.1 s30.2.2 f32 f20
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f01
  | 0, 2, _ => exact f02
  | 0, 3, _ => exact f03
  | 1, 0, _ => exact f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f12
  | 1, 3, _ => exact f13
  | 2, 0, _ => exact f20
  | 2, 1, _ => exact f21
  | 2, 2, h => exact absurd rfl h
  | 2, 3, _ => exact f23
  | 3, 0, _ => exact f30
  | 3, 1, _ => exact f31
  | 3, 2, _ => exact f32
  | 3, 3, h => exact absurd rfl h

theorem a3Rep_surjective : Function.Surjective (a3Rep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, hε, h⟩ := a3RootFamily_all (K := K) i j hij
  have hmem := pinnedX_mem_a3Group (chainRoot134_mem_parabolicRoots hij) ((ε : K) * c)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [coe_a3Rep, h, CFSG.LinearGroups.coe_transvection]
  congr 1
  rcases hε with rfl | rfl <;> simp

theorem a3TorusElt_mul (a b c a' b' c' : Kˣ) :
    a3TorusElt a b c * a3TorusElt a' b' c' = a3TorusElt (a * a') (b * b') (c * c') := by
  simp only [a3TorusElt, torusElt_mul]
  have h1 := torusElt_mul_comm (τ := Tag.E6) (R := K) (e6Index 3) (e6Index 0) c a'
  have h2 := torusElt_mul_comm (τ := Tag.E6) (R := K) (e6Index 2) (e6Index 0) b a'
  have h3 := torusElt_mul_comm (τ := Tag.E6) (R := K) (e6Index 3) (e6Index 2) c b'
  calc torusElt Tag.E6 K (e6Index 0) a * torusElt Tag.E6 K (e6Index 2) b *
        torusElt Tag.E6 K (e6Index 3) c * (torusElt Tag.E6 K (e6Index 0) a' *
          torusElt Tag.E6 K (e6Index 2) b' * torusElt Tag.E6 K (e6Index 3) c')
      = torusElt Tag.E6 K (e6Index 0) a * torusElt Tag.E6 K (e6Index 2) b *
          (torusElt Tag.E6 K (e6Index 3) c * torusElt Tag.E6 K (e6Index 0) a') *
            torusElt Tag.E6 K (e6Index 2) b' * torusElt Tag.E6 K (e6Index 3) c' := by group
    _ = torusElt Tag.E6 K (e6Index 0) a * (torusElt Tag.E6 K (e6Index 2) b *
          torusElt Tag.E6 K (e6Index 0) a') * (torusElt Tag.E6 K (e6Index 3) c *
            torusElt Tag.E6 K (e6Index 2) b') * torusElt Tag.E6 K (e6Index 3) c' := by
        rw [h1]; group
    _ = _ := by rw [h2, h3]; group

theorem a3TorusElt_one : a3TorusElt (1 : Kˣ) 1 1 = 1 := by
  simp only [a3TorusElt, torusElt_one, mul_one]

theorem a3TorusElt_inv (a b c : Kˣ) : (a3TorusElt a b c)⁻¹ = a3TorusElt a⁻¹ b⁻¹ c⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [a3TorusElt_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, a3TorusElt_one]

theorem mem_subsystemTorus_a3 {g : ModGL Tag.E6 K} :
    g ∈ subsystemTorus Tag.E6 K support134 ↔ ∃ a b c : Kˣ, g = a3TorusElt a b c := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, t, rfl⟩ := hx
      rcases (mem_support134 i).1 hi with rfl | rfl | rfl
      · exact ⟨t, 1, 1, by simp only [a3TorusElt, torusElt_one, mul_one]⟩
      · exact ⟨1, t, 1, by simp only [a3TorusElt, torusElt_one, mul_one, one_mul]⟩
      · exact ⟨1, 1, t, by simp only [a3TorusElt, torusElt_one, one_mul]⟩
    | one => exact ⟨1, 1, 1, a3TorusElt_one.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, c, rfl⟩ := hx
      obtain ⟨a', b', c', rfl⟩ := hy
      exact ⟨_, _, _, a3TorusElt_mul a b c a' b' c'⟩
    | inv x _ hx =>
      obtain ⟨a, b, c, rfl⟩ := hx
      exact ⟨_, _, _, a3TorusElt_inv a b c⟩
  · rintro ⟨a, b, c, rfl⟩
    exact mul_mem (mul_mem (torusElt_mem_subsystemTorus mem_support134_0 a)
      (torusElt_mem_subsystemTorus mem_support134_2 b))
      (torusElt_mem_subsystemTorus mem_support134_3 c)

theorem list_prod_weylElt_rootVec_E6 (ω : List (Fin Tag.E6.rank)) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) : ∃ ε : K, ε ≠ 0 ∧
      (((ω.map fun i => weylElt Tag.E6 K i 1).prod : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
      ε • rootVec Tag.E6 K ((coxeterSystem Tag.E6).wordProd ω • β) := by
  induction ω with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨ε * ((-1) ^ stringDown Tag.E6 i ((coxeterSystem Tag.E6).wordProd ω • β) *
      (((1 : Kˣ) ^ (-∑ j, Tag.E6.cartan i j * ((coxeterSystem Tag.E6).wordProd ω • β) j) : Kˣ) :
        K)), mul_ne_zero hε (by simp), ?_⟩
    have e : (coxeterSystem Tag.E6).wordProd (i :: ω) • β =
        reflect Tag.E6 i ((coxeterSystem Tag.E6).wordProd ω • β) := by
      rw [CoxeterSystem.wordProd_cons, mul_smul]
      exact simple_smul i _
    rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
      weylElt_rootVec i 1 (IsRoot.smul hβ _), smul_smul]

theorem canonicalRep_rootVec_E6 (w : WeylGroup Tag.E6) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) : ∃ ε : K, ε ≠ 0 ∧
      (canonicalRep (coxeterSystem Tag.E6) K w : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K β) = ε • rootVec Tag.E6 K (w • β) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact list_prod_weylElt_rootVec_E6 ω hβ

theorem a3Weight_height : ∀ i j : Fin 4,
    (height (a3Weight j) < height (a3Weight i) ↔ i < j) ∧
      (height (a3Weight i) = height (a3Weight j) ↔ i = j) := by
  decide

theorem a3Label_precedes_iff (i j : Fin 4) : (a3Label i).Precedes (a3Label j) ↔ i < j := by
  simp only [Label.Precedes, Label.weight]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact ((a3Weight_height i j).1).1 h
    · obtain rfl := ((a3Weight_height i j).2).1 h
      exact absurd h' (lt_irrefl _)
  · intro h
    exact Or.inl (((a3Weight_height i j).1).2 h)

theorem not_mem_support134 : e6Index 1 ∉ support134 ∧ e6Index 4 ∉ support134 ∧
    e6Index 5 ∉ support134 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    rcases (mem_support134 _).1 h with h | h | h <;> exact absurd h (by decide)

theorem a3Weight_outside : ∀ k : Fin 4, a3Weight k (e6Index 1) = 0 ∧
    a3Weight k (e6Index 4) = 1 ∧ a3Weight k (e6Index 5) = 0 := by
  decide

theorem exists_a3Weight_of_e6RootVec : ∀ m : Fin 72, e6RootVec m (e6Index 1) = 0 →
    e6RootVec m (e6Index 4) = 1 → e6RootVec m (e6Index 5) = 0 →
      ∃ k, a3Weight k = e6RootVec m := by
  decide +kernel

theorem exists_a3Weight_smul {w : WeylGroup Tag.E6}
    (hw : w ∈ parabolicWeylGroup Tag.E6 support134) (k : Fin 4) :
    ∃ k', a3Weight k' = w • a3Weight k := by
  obtain ⟨n1, n4, n5⟩ := not_mem_support134
  obtain ⟨a1, a4, a5⟩ := a3Weight_outside k
  obtain ⟨m, hm⟩ := isRoot_iff_exists_e6RootVec.1 (IsRoot.smul (isRoot_a3Weight k) w)
  obtain ⟨k', hk'⟩ := exists_a3Weight_of_e6RootVec m
    (by rw [hm, smul_apply_of_mem_parabolicWeylGroup hw _ n1, a1])
    (by rw [hm, smul_apply_of_mem_parabolicWeylGroup hw _ n4, a4])
    (by rw [hm, smul_apply_of_mem_parabolicWeylGroup hw _ n5, a5])
  exact ⟨k', hk'.trans hm⟩

theorem smul_a3Weight_eq_of_not_lt {w : WeylGroup Tag.E6}
    (hw : w ∈ parabolicWeylGroup Tag.E6 support134)
    (hprec : ∀ j j', a3Weight j' = w • a3Weight j → ¬j < j') (j : Fin 4) :
    w • a3Weight j = a3Weight j := by
  by_contra hj
  classical
  set M : Finset (Fin 4) := Finset.univ.filter fun k => w • a3Weight k ≠ a3Weight k
  have hM : M.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨k, hkM, hmin⟩ := M.exists_min_image id hM
  have hk : w • a3Weight k ≠ a3Weight k := (Finset.mem_filter.mp hkM).2
  obtain ⟨k', hk'⟩ := exists_a3Weight_smul hw k
  have hne : k' ≠ k := fun h => hk (by rw [← hk', h])
  have hlt : k' < k := lt_of_le_of_ne (not_lt.1 (hprec k k' hk')) hne
  have hk'M : k' ∈ M := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne ?_⟩
    apply a3Weight_injective
    apply smul_left_cancel w
    rw [h]
    exact hk'
  exact absurd (hmin k' hk'M) (not_le.mpr hlt)

theorem single_eq_a3Weight_sub :
    (Pi.single (e6Index 0) 1 : Fin Tag.E6.rank → ℤ) = a3Weight 0 - a3Weight 1 ∧
    (Pi.single (e6Index 2) 1 : Fin Tag.E6.rank → ℤ) = a3Weight 1 - a3Weight 2 ∧
    (Pi.single (e6Index 3) 1 : Fin Tag.E6.rank → ℤ) = a3Weight 2 - a3Weight 3 := by
  decide

theorem eq_one_of_smul_a3Weight {w : WeylGroup Tag.E6}
    (hw : w ∈ parabolicWeylGroup Tag.E6 support134) (h : ∀ k, w • a3Weight k = a3Weight k) :
    w = 1 := by
  obtain ⟨e0, e2, e3⟩ := single_eq_a3Weight_sub
  refine eq_one_of_forall_height_pos fun i => ?_
  by_cases hi : i ∈ support134
  · have hfix : w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = Pi.single i 1 := by
      rcases (mem_support134 i).1 hi with rfl | rfl | rfl
      · rw [e0, smul_sub, h, h]
      · rw [e2, smul_sub, h, h]
      · rw [e3, smul_sub, h, h]
    rw [hfix, height_single]
    exact one_pos
  · have hroot := IsRoot.smul (isRoot_single Tag.E6 i) w
    have hcoord : (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) i = 1 := by
      rw [smul_apply_of_mem_parabolicWeylGroup hw _ hi, Pi.single_eq_same]
    refine (IsRoot.height_pos_iff hroot).2 ?_
    rcases hroot.nonneg_or_nonpos with hs | hs
    · exact hs
    · have := hs i
      omega

theorem borel_apply_a3Vec_eq_zero {c : ModGL Tag.E6 K} (hc : c ∈ borelGroup Tag.E6 K)
    {j j' : Fin 4} (h : j < j') :
    (c : Module.End K (RootModule Tag.E6 K)) (a3Vec K j) (a3Label j') = 0 :=
  (triangular_borel_structure.{0, 0} Tag.E6 K).2.2.2.2.2.2.2.2.2.1 c hc (a3Label j')
    (a3Label j) ((a3Label_precedes_iff j j').2 h)

@[expose] def a3PosRoot : Fin 6 → Fin Tag.E6.rank → ℤ :=
  ![chainRoot chain134 2 3, chainRoot chain134 1 2, chainRoot chain134 1 3,
    chainRoot chain134 0 1, chainRoot chain134 0 2, chainRoot chain134 0 3]

theorem a3PosRoot_injective : Function.Injective a3PosRoot := by
  intro k k' h
  revert k k'
  decide +kernel

theorem chainRoot134_height_pos : ∀ k l : Fin 4, k ≠ l →
    (0 < height (chainRoot chain134 k l) ↔ k < l) := by
  decide +kernel

theorem exists_a3PosRoot : ∀ k l : Fin 4, k < l → ∃ m, a3PosRoot m = chainRoot chain134 k l := by
  decide +kernel

theorem range_a3PosRoot : Set.range a3PosRoot = parabolicPosRoots Tag.E6 support134 := by
  ext β
  constructor
  · rintro ⟨m, rfl⟩
    have h : ∀ m : Fin 6, ∃ k l : Fin 4, k < l ∧ a3PosRoot m = chainRoot chain134 k l := by
      decide
    obtain ⟨k, l, hkl, hm⟩ := h m
    rw [hm]
    have hmem := chainRoot134_mem_parabolicRoots hkl.ne
    exact ⟨hmem, hmem.1, (chainRoot134_height_pos k l hkl.ne).2 hkl⟩
  · rintro ⟨hβ, -, hpos⟩
    obtain ⟨k, l, hkl, rfl⟩ := exists_chainRoot_of_mem hβ
    exact exists_a3PosRoot k l ((chainRoot134_height_pos k l hkl).1 hpos)

@[expose] def a3PosRow : Fin 6 → Fin 4 := ![2, 1, 1, 0, 0, 0]

@[expose] def a3PosCol : Fin 6 → Fin 4 := ![3, 2, 3, 1, 2, 3]

theorem a3PosRoot_eq (m : Fin 6) : a3PosRoot m = chainRoot chain134 (a3PosRow m) (a3PosCol m) := by
  fin_cases m <;> rfl

theorem a3PosRow_lt_col : ∀ m : Fin 6, a3PosRow m < a3PosCol m := by decide

theorem one_add_mul_one_add {A S : Matrix (Fin 4) (Fin 4) K} (h : A * S = 0) :
    (1 + A) * (1 + S) = 1 + (A + S) := by
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h, add_zero]
  abel

theorem single_mul_single_eq_zero {p q r s : Fin 4} (h : q ≠ r) (a b : K) :
    (single p q a : Matrix (Fin 4) (Fin 4) K) * single r s b = 0 :=
  single_mul_single_of_ne a p q r h b

theorem prod_a3Pos (x : Fin 6 → K) :
    (List.ofFn fun m => (1 + single (a3PosRow m) (a3PosCol m) (x m) :
      Matrix (Fin 4) (Fin 4) K)).prod =
      1 + (single 2 3 (x 0) + (single 1 2 (x 1) + (single 1 3 (x 2) + (single 0 1 (x 3) +
        (single 0 2 (x 4) + single 0 3 (x 5)))))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  change (1 + single 2 3 (x 0)) * ((1 + single 1 2 (x 1)) * ((1 + single 1 3 (x 2)) *
    ((1 + single 0 1 (x 3)) * ((1 + single 0 2 (x 4)) * (1 + single 0 3 (x 5)))))) = _
  have z20 : ∀ (s : Fin 4) (a b : K),
      (single 0 2 a : Matrix (Fin 4) (Fin 4) K) * single 0 s b = 0 :=
    fun s a b => single_mul_single_eq_zero (by decide) a b
  have z10 : ∀ (s : Fin 4) (a b : K),
      (single 0 1 a : Matrix (Fin 4) (Fin 4) K) * single 0 s b = 0 :=
    fun s a b => single_mul_single_eq_zero (by decide) a b
  have z30 : ∀ (s : Fin 4) (a b : K),
      (single 1 3 a : Matrix (Fin 4) (Fin 4) K) * single 0 s b = 0 :=
    fun s a b => single_mul_single_eq_zero (by decide) a b
  have z21 : ∀ (r s : Fin 4) (a b : K), r ≠ 2 →
      (single 1 2 a : Matrix (Fin 4) (Fin 4) K) * single r s b = 0 :=
    fun r s a b h => single_mul_single_eq_zero (Ne.symm h) a b
  have z31 : ∀ (r s : Fin 4) (a b : K), r ≠ 3 →
      (single 2 3 a : Matrix (Fin 4) (Fin 4) K) * single r s b = 0 :=
    fun r s a b h => single_mul_single_eq_zero (Ne.symm h) a b
  rw [one_add_mul_one_add (z20 3 _ _),
    one_add_mul_one_add (by rw [Matrix.mul_add, z10, z10, add_zero]),
    one_add_mul_one_add (by rw [Matrix.mul_add, Matrix.mul_add, z30, z30, z30, add_zero,
      add_zero]),
    one_add_mul_one_add (by rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
      z21 1 3 _ _ (by decide), z21 0 1 _ _ (by decide), z21 0 2 _ _ (by decide),
      z21 0 3 _ _ (by decide), add_zero, add_zero, add_zero]),
    one_add_mul_one_add (by rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
      z31 1 2 _ _ (by decide), z31 1 3 _ _ (by decide), z31 0 1 _ _ (by decide),
      z31 0 2 _ _ (by decide), z31 0 3 _ _ (by decide), add_zero, add_zero, add_zero,
      add_zero])]

theorem a3Mat_list_prod (l : List (ModGL Tag.E6 K))
    (hl : ∀ g ∈ l, g ∈ subsystemGroup Tag.E6 K support134) :
    a3Mat l.prod = (l.map a3Mat).prod := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil, a3Mat_one]
  | cons g l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      a3Mat_mul (hl g List.mem_cons_self) (Subgroup.list_prod_mem _ fun h hh => hl h
        (List.mem_cons_of_mem g hh)), ih fun h hh => hl h (List.mem_cons_of_mem g hh)]

theorem a3PosRoot_mem (m : Fin 6) : a3PosRoot m ∈ parabolicRoots Tag.E6 support134 :=
  (show a3PosRoot m ∈ parabolicPosRoots Tag.E6 support134 from range_a3PosRoot ▸ ⟨m, rfl⟩).1

theorem eq_one_of_a3Mat_mul_eq_one {t u : ModGL Tag.E6 K}
    (ht : t ∈ subsystemTorus Tag.E6 K support134)
    (hu : u ∈ parabolicLeviUnipotent Tag.E6 K support134) (h : a3Mat (t * u) = 1) :
    t = 1 ∧ u = 1 := by
  obtain ⟨a, b, c, rfl⟩ := mem_subsystemTorus_a3.1 ht
  obtain ⟨x, -, rfl⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) a3PosRoot
    a3PosRoot_injective range_a3PosRoot).surjOn hu
  choose ε hε hfam using a3RootFamily_all (K := K)
  have hrc : ∀ m, a3PosRow m ≠ a3PosCol m := fun m => (a3PosRow_lt_col m).ne
  set y : Fin 6 → K := fun m => (ε (a3PosRow m) (a3PosCol m) (hrc m) : K) * x m with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.E6 K (a3PosRoot m) (x m),
      g ∈ subsystemGroup Tag.E6 K support134 := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact pinnedX_mem_a3Group (a3PosRoot_mem m) _
  have hu' : a3Mat (List.ofFn fun m => pinnedX Tag.E6 K (a3PosRoot m) (x m)).prod =
      1 + (single 2 3 (y 0) + (single 1 2 (y 1) + (single 1 3 (y 2) + (single 0 1 (y 3) +
        (single 0 2 (y 4) + single 0 3 (y 5)))))) := by
    rw [a3Mat_list_prod _ hlist, List.map_ofFn, ← prod_a3Pos y]
    refine congrArg List.prod (congrArg List.ofFn (funext fun m => ?_))
    rw [Function.comp_apply, a3PosRoot_eq, hfam]
  rw [a3Mat_mul (a3TorusElt_mem a b c) (Subgroup.list_prod_mem _ hlist), a3Mat_a3TorusElt, hu'] at h
  have e : ∀ p q, (Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ * c : Kˣ) : K),
      ((c⁻¹ : Kˣ) : K)] * (1 + (single 2 3 (y 0) + (single 1 2 (y 1) + (single 1 3 (y 2) +
        (single 0 1 (y 3) + (single 0 2 (y 4) + single 0 3 (y 5))))))) : Matrix (Fin 4) (Fin 4) K)
        p q = (1 : Matrix (Fin 4) (Fin 4) K) p q := fun p q => by rw [h]
  have d0 := e 0 0
  have d1 := e 1 1
  have d2 := e 2 2
  simp [Matrix.diagonal_mul, Matrix.add_apply] at d0 d1 d2
  have ha : a = 1 := Units.ext (by simpa using d0)
  subst ha
  have hb : b = 1 := Units.ext (by simpa using d1)
  subst hb
  have hc : c = 1 := Units.ext (by simpa using d2)
  subst hc
  have o0 := e 2 3
  have o1 := e 1 2
  have o2 := e 1 3
  have o3 := e 0 1
  have o4 := e 0 2
  have o5 := e 0 3
  simp [Matrix.diagonal_mul, Matrix.add_apply] at o0 o1 o2 o3 o4 o5
  have hy0 : ∀ m, y m = 0 := by
    intro m
    fin_cases m
    exacts [o0, o1, o2, o3, o4, o5]
  have hx0 : x = 0 := by
    funext m
    have h0 := hy0 m
    rw [hy] at h0
    rcases hε (a3PosRow m) (a3PosCol m) (hrc m) with h1 | h1 <;>
      (simp only [h1] at h0; simpa using h0)
  subst hx0
  refine ⟨a3TorusElt_one, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem a3Rep_injective : Function.Injective (a3Rep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : a3Mat (g : ModGL Tag.E6 K) = 1 := congrArg Subtype.val hg
  have hfixv : ∀ k, ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (a3Vec K k) =
      a3Vec K k := by
    intro k
    rw [apply_a3Vec g.2, hmat]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hfix : ∀ m ∈ a3Module K, ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) m =
      m := by
    intro m hm
    have e := eq_sum_of_mem_a3Module hm
    calc ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) m =
        ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
          (∑ k, m (a3Label k) • a3Vec K k) := by rw [← e]
      _ = ∑ k, m (a3Label k) • a3Vec K k := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hfixv]
      _ = m := e.symm
  have hgS : (g : ModGL Tag.E6 K) ∈
      (subsystemGroup Tag.E6 K support134 : Set (ModGL Tag.E6 K)) := g.2
  rw [(subsystem_root_group_bruhat (τ := Tag.E6) (K := K) (A := support134)).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w, hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup Tag.E6 K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent Tag.E6 K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup Tag.E6 K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ subsystemGroup Tag.E6 K support134 :=
    parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E6) (K := K) (A := support134)
      (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem Tag.E6) K w : Module.End K (RootModule Tag.E6 K))
      (a3Vec K j) = ((b⁻¹ * v⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
        (a3Vec K j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem Tag.E6) K w = b⁻¹ * (g : ModGL Tag.E6 K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (mem_a3Module_of_mem (inv_mem hvS) (a3Vec_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j', a3Weight j' = w • a3Weight j → ¬j < j' := by
    intro j j' hj' hlt
    obtain ⟨ε, hε, hne⟩ := canonicalRep_rootVec_E6 (K := K) w (isRoot_a3Weight j)
    have h0 := borel_apply_a3Vec_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hlt
    rw [← hn j, ← rootVec_a3Weight, hne, ← hj', rootVec_a3Weight, Finsupp.smul_apply,
      a3Vec_apply, ite_eq_left rfl, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w = 1 := eq_one_of_smul_a3Weight hw (smul_a3Weight_eq_of_not_lt hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan Tag.E6 K (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (subsystemTorus Tag.E6 K support134 : Set (ModGL Tag.E6 K)) *
      (parabolicLeviUnipotent Tag.E6 K support134 : Set (ModGL Tag.E6 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.E6) (K := K) (A := support134)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  beta_reduce at hgbv
  have h1 := eq_one_of_a3Mat_mul_eq_one ht hu (by rw [hgbv]; exact hmat)
  refine Subtype.ext ?_
  rw [Subgroup.coe_one, ← hgbv, h1.1, h1.2, mul_one]

theorem baseChangeGL_mem_a3Group {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K support134) :
    baseChangeGL σ g ∈ subsystemGroup Tag.E6 L support134 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit]
      exact xUnit_mem_subsystemGroup hi _
    · rw [baseChangeGL_yUnit]
      exact yUnit_mem_subsystemGroup hi _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem map_single_ringHom {L : Type} [Field L] (σ : K →+* L) (p q : Fin 4) (c : K) :
    (single p q c : Matrix (Fin 4) (Fin 4) K).map σ = single p q (σ c) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem a3Mat_baseChangeGL {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K support134) :
    a3Mat (baseChangeGL σ g) = (a3Mat g).map σ := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit]
      rcases (mem_support134 i).1 hi with rfl | rfl | rfl
      · rw [a3Mat_x1, a3Mat_x1, Matrix.map_add _ (map_add σ), Matrix.map_one _ σ.map_zero σ.map_one,
          map_single_ringHom]
      · rw [a3Mat_x3, a3Mat_x3, Matrix.map_add _ (map_add σ), Matrix.map_one _ σ.map_zero σ.map_one,
          map_single_ringHom]
      · rw [a3Mat_x4, a3Mat_x4, Matrix.map_add _ (map_add σ), Matrix.map_one _ σ.map_zero σ.map_one,
          map_single_ringHom]
    · rw [baseChangeGL_yUnit]
      rcases (mem_support134 i).1 hi with rfl | rfl | rfl
      · rw [a3Mat_y1, a3Mat_y1, Matrix.map_add _ (map_add σ), Matrix.map_one _ σ.map_zero σ.map_one,
          map_single_ringHom]
      · rw [a3Mat_y3, a3Mat_y3, Matrix.map_add _ (map_add σ), Matrix.map_one _ σ.map_zero σ.map_one,
          map_single_ringHom]
      · rw [a3Mat_y4, a3Mat_y4, Matrix.map_add _ (map_add σ), Matrix.map_one _ σ.map_zero σ.map_one,
          map_single_ringHom]
  | one => rw [map_one, a3Mat_one, a3Mat_one, Matrix.map_one _ σ.map_zero σ.map_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, a3Mat_mul (baseChangeGL_mem_a3Group σ hx) (baseChangeGL_mem_a3Group σ hy), ihx,
      ihy, a3Mat_mul hx hy, Matrix.map_mul]
  | inv x hx ih =>
    have hL := baseChangeGL_mem_a3Group σ hx
    rw [map_inv, a3Mat_inv hL, ih]
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.map_mul, ← a3Mat_mul (inv_mem hx) hx, inv_mul_cancel, a3Mat_one,
      Matrix.map_one _ σ.map_zero σ.map_one]

theorem E6_native_A3_faithful_SL4_all_characteristics (K : Type) [Field K] :
    Function.Bijective (a3Rep K) ∧
    (∀ (g : subsystemGroup Tag.E6 K support134) (j : Fin 4),
      ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (a3Vec K j) =
        ∑ i, (a3Rep K g : Matrix (Fin 4) (Fin 4) K) i j • a3Vec K i) ∧
    (∀ t : K, a3Mat (xUnit Tag.E6 K (e6Index 0) t) = 1 + single 0 1 t) ∧
    (∀ t : K, a3Mat (yUnit Tag.E6 K (e6Index 0) t) = 1 + single 1 0 t) ∧
    (∀ t : K, a3Mat (xUnit Tag.E6 K (e6Index 2) t) = 1 + single 1 2 t) ∧
    (∀ t : K, a3Mat (yUnit Tag.E6 K (e6Index 2) t) = 1 + single 2 1 t) ∧
    (∀ t : K, a3Mat (xUnit Tag.E6 K (e6Index 3) t) = 1 + single 2 3 t) ∧
    (∀ t : K, a3Mat (yUnit Tag.E6 K (e6Index 3) t) = 1 + single 3 2 t) ∧
    (∀ a b c : Kˣ, a3Mat (a3TorusElt a b c) =
      Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ * c : Kˣ) : K), ((c⁻¹ : Kˣ) : K)]) ∧
    subsystemGroup Tag.E6 K support134 = rootSpan Tag.E6 K (parabolicRoots Tag.E6 support134) ∧
    (∀ g : ModGL Tag.E6 K, g ∈ subsystemGroup Tag.E6 K support134 ⊓ torusGroup Tag.E6 K ↔
      ∃ a b c : Kˣ, g = a3TorusElt a b c) ∧
    (∀ i j : Fin 4, i ≠ j → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
      a3Mat (pinnedX Tag.E6 K (chainRoot chain134 i j) t) = 1 + single i j ((ε : K) * t)) ∧
    (∀ (L : Type) [Field L] (σ : K →+* L) (g : ModGL Tag.E6 K),
      g ∈ subsystemGroup Tag.E6 K support134 →
        baseChangeGL σ g ∈ subsystemGroup Tag.E6 L support134 ∧
          a3Mat (baseChangeGL σ g) = (a3Mat g).map σ) ∧
    (∀ l : K, l ^ 4 = 1 → ∃ g ∈ Subgroup.center (subsystemGroup Tag.E6 K support134),
      (a3Rep K g : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) l) := by
  have hbij : Function.Bijective (a3Rep K) := ⟨a3Rep_injective, a3Rep_surjective⟩
  refine ⟨hbij, fun g j => apply_a3Vec g.2 j, a3Mat_x1, a3Mat_y1, a3Mat_x3, a3Mat_y3, a3Mat_x4,
    a3Mat_y4, a3Mat_a3TorusElt, subsystemGroup_eq_rootSpan support134, fun g => ?_,
    a3RootFamily_all, fun L _ σ g hg => ⟨baseChangeGL_mem_a3Group σ hg, a3Mat_baseChangeGL σ hg⟩,
    fun l hl => ?_⟩
  · rw [subsystemGroup_inf_torusGroup, mem_subsystemTorus_a3]
  ·
    have hdet : (Matrix.scalar (Fin 4) l).det = 1 := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hl]
    set s : SpecialLinearGroup (Fin 4) K := ⟨Matrix.scalar (Fin 4) l, hdet⟩
    obtain ⟨g, hg⟩ := hbij.2 s
    refine ⟨g, Subgroup.mem_center_iff.2 fun h => hbij.1 ?_, by rw [hg]⟩
    rw [map_mul, map_mul, hg]
    refine Subtype.ext ?_
    change (a3Rep K h : Matrix (Fin 4) (Fin 4) K) * Matrix.scalar (Fin 4) l =
      Matrix.scalar (Fin 4) l * (a3Rep K h : Matrix (Fin 4) (Fin 4) K)
    exact (Matrix.scalar_commute l (fun r => Commute.all l r) _).eq.symm

end CFSG.RankThree.E6
