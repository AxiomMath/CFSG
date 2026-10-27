module

public import CFSG.RankThree.PartOne.KE.E7A2NativeModule

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped commutatorElement Pointwise MatrixGroups

@[expose] def e7a6support : Set (Fin Tag.E7.rank) :=
  {e7Index 0, e7Index 2, e7Index 3, e7Index 4, e7Index 5, e7Index 6}

theorem mem_e7a6support (i : Fin Tag.E7.rank) :
    i ∈ e7a6support ↔ (i = e7Index 0 ∨ i = e7Index 2 ∨ i = e7Index 3 ∨ i = e7Index 4 ∨ i = e7Index 5 ∨ i = e7Index 6) := by
  simp only [e7a6support, Set.mem_insert_iff, Set.mem_singleton_iff]

@[expose] def e7a6chain : Fin 6 → Fin Tag.E7.rank :=
  ![e7Index 0, e7Index 2, e7Index 3, e7Index 4, e7Index 5, e7Index 6]

theorem mem_e7a6support_0 : e7Index 0 ∈ e7a6support :=
  (mem_e7a6support _).2 (Or.inl rfl)

theorem mem_e7a6support_2 : e7Index 2 ∈ e7a6support :=
  (mem_e7a6support _).2 (Or.inr (Or.inl rfl))

theorem mem_e7a6support_3 : e7Index 3 ∈ e7a6support :=
  (mem_e7a6support _).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem mem_e7a6support_4 : e7Index 4 ∈ e7a6support :=
  (mem_e7a6support _).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem mem_e7a6support_5 : e7Index 5 ∈ e7a6support :=
  (mem_e7a6support _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

theorem mem_e7a6support_6 : e7Index 6 ∈ e7a6support :=
  (mem_e7a6support _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

@[expose] def e7a6Weight : Fin 7 → Fin Tag.E7.rank → ℤ :=
  (![![2, 2, 3, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 2, 1, 1],
    ![1, 2, 2, 3, 2, 1, 0]] : Fin 7 → Fin 7 → ℤ)

theorem exists_e7RootVec_e7a6Weight : ∀ k : Fin 7, ∃ m : Fin 126, e7RootVec m = e7a6Weight k := by
  decide +kernel

theorem isRoot_e7a6Weight (k : Fin 7) : IsRoot Tag.E7 (e7a6Weight k) := by
  obtain ⟨m, hm⟩ := exists_e7RootVec_e7a6Weight k
  rw [← hm]
  exact isRoot_e7RootVec m

theorem e7a6Weight_injective : Function.Injective e7a6Weight := by
  intro k k' h
  revert k k'
  decide

abbrev e7a6Label (k : Fin 7) : Label Tag.E7 := Sum.inr ⟨e7a6Weight k, isRoot_e7a6Weight k⟩

theorem e7a6Label_injective : Function.Injective e7a6Label := by
  intro k k' h
  exact e7a6Weight_injective (congrArg Subtype.val (Sum.inr_injective h))

variable (K : Type) [Field K]

@[expose] def e7a6Vec (k : Fin 7) : RootModule Tag.E7 K := Finsupp.single (e7a6Label k) 1

theorem rootVec_e7a6Weight (k : Fin 7) : rootVec Tag.E7 K (e7a6Weight k) = e7a6Vec K k :=
  CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K (isRoot_e7a6Weight k)

variable {K}

theorem e7a6Vec_apply (k i : Fin 7) : e7a6Vec K k (e7a6Label i) = if i = k then 1 else 0 := by
  rw [e7a6Vec, Finsupp.single_apply]
  by_cases h : i = k
  · rw [ite_eq_left (congrArg e7a6Label h).symm, ite_eq_left h]
  · rw [ite_eq_right fun e => h (e7a6Label_injective e).symm, ite_eq_right h]

theorem rootVec_apply_e7a6Label (γ : Fin Tag.E7.rank → ℤ) (i : Fin 7) :
    rootVec Tag.E7 K γ (e7a6Label i) = if γ = e7a6Weight i then 1 else 0 := by
  by_cases hγ : IsRoot Tag.E7 γ
  · rw [CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K hγ, Finsupp.single_apply]
    by_cases h : γ = e7a6Weight i
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [rootVec_eq_zero_of_not_isRoot hγ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hγ (isRoot_e7a6Weight i)

variable (K) in
@[expose] def e7a6Module : Submodule K (RootModule Tag.E7 K) :=
  Submodule.span K (Set.range (e7a6Vec K))

theorem e7a6Vec_mem (k : Fin 7) : e7a6Vec K k ∈ e7a6Module K :=
  Submodule.subset_span ⟨k, rfl⟩

theorem eq_sum_of_mem_e7a6Module {m : RootModule Tag.E7 K} (hm : m ∈ e7a6Module K) :
    m = ∑ k, m (e7a6Label k) • e7a6Vec K k := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [e7a6Vec_apply, ite_eq_right hj, zero_smul])
      (by simp), e7a6Vec_apply, ite_eq_left rfl, one_smul]
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

theorem rootVec_mem_e7a6Module {γ : Fin Tag.E7.rank → ℤ}
    (h : (∀ m : Fin 126, e7RootVec m ≠ γ) ∨ ∃ k, e7a6Weight k = γ) :
    rootVec Tag.E7 K γ ∈ e7a6Module K := by
  rcases h with h | ⟨k, rfl⟩
  · have hγ : ¬IsRoot Tag.E7 γ := fun hγ => by
      obtain ⟨m, hm⟩ := isRoot_iff_exists_e7RootVec.1 hγ
      exact h m hm
    rw [rootVec_eq_zero_of_not_isRoot hγ]
    exact zero_mem _
  · rw [rootVec_e7a6Weight]
    exact e7a6Vec_mem k

theorem e7a6Weight_ne_single : ∀ k : Fin 7, ∀ i : Fin 7, (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) →
    e7a6Weight k ≠ Pi.single (e7Index i) 1 ∧ e7a6Weight k ≠ -Pi.single (e7Index i) 1 := by
  decide +kernel

theorem e7a6Weight_add_single : ∀ k : Fin 7, ∀ i : Fin 7, (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) →
    (∀ m : Fin 126, e7RootVec m ≠ e7a6Weight k + Pi.single (e7Index i) 1) ∨
      ∃ k', e7a6Weight k' = e7a6Weight k + Pi.single (e7Index i) 1 := by
  decide +kernel

theorem e7a6Weight_sub_single : ∀ k : Fin 7, ∀ i : Fin 7, (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) →
    (∀ m : Fin 126, e7RootVec m ≠ e7a6Weight k - Pi.single (e7Index i) 1) ∨
      ∃ k', e7a6Weight k' = e7a6Weight k - Pi.single (e7Index i) 1 := by
  decide +kernel

theorem xOp_e7a6Vec {i : Fin Tag.E7.rank} (hi : i ∈ e7a6support) (c : K) (k : Fin 7) :
    xOp Tag.E7 K i c (e7a6Vec K k) =
      e7a6Vec K k + c • rootVec Tag.E7 K (e7a6Weight k + Pi.single i 1) := by
  rw [← rootVec_e7a6Weight]
  exact xOp_rootVec_E7 i c (isRoot_e7a6Weight k)
    (e7a6Weight_ne_single k i ((mem_e7a6support i).1 hi)).1
    (e7a6Weight_ne_single k i ((mem_e7a6support i).1 hi)).2

theorem yOp_e7a6Vec {i : Fin Tag.E7.rank} (hi : i ∈ e7a6support) (c : K) (k : Fin 7) :
    yOp Tag.E7 K i c (e7a6Vec K k) =
      e7a6Vec K k + c • rootVec Tag.E7 K (e7a6Weight k - Pi.single i 1) := by
  rw [← rootVec_e7a6Weight]
  exact yOp_rootVec_E7 i c (isRoot_e7a6Weight k)
    (e7a6Weight_ne_single k i ((mem_e7a6support i).1 hi)).1
    (e7a6Weight_ne_single k i ((mem_e7a6support i).1 hi)).2

theorem mem_e7a6Module_of_mem {g : ModGL Tag.E7 K}
    (hg : g ∈ subsystemGroup Tag.E7 K e7a6support)
    {m : RootModule Tag.E7 K} (hm : m ∈ e7a6Module K) :
    (g : Module.End K (RootModule Tag.E7 K)) m ∈ e7a6Module K := by
  refine mem_of_mem_subsystemGroup_of_invariant (fun i hi c v hv => ?_)
    (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [xOp_e7a6Vec hi]
      exact add_mem (e7a6Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_e7a6Module (e7a6Weight_add_single k i ((mem_e7a6support i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [yOp_e7a6Vec hi]
      exact add_mem (e7a6Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_e7a6Module (e7a6Weight_sub_single k i ((mem_e7a6support i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

@[expose] def e7a6Mat (g : ModGL Tag.E7 K) : Matrix (Fin 7) (Fin 7) K :=
  Matrix.of fun i j => (g : Module.End K (RootModule Tag.E7 K)) (e7a6Vec K j) (e7a6Label i)

theorem apply_e7a6Vec {g : ModGL Tag.E7 K} (hg : g ∈ subsystemGroup Tag.E7 K e7a6support)
    (j : Fin 7) :
    (g : Module.End K (RootModule Tag.E7 K)) (e7a6Vec K j) = ∑ i, e7a6Mat g i j • e7a6Vec K i :=
  eq_sum_of_mem_e7a6Module (mem_e7a6Module_of_mem hg (e7a6Vec_mem j))

theorem e7a6Mat_one : e7a6Mat (1 : ModGL Tag.E7 K) = 1 := by
  ext i j
  rw [e7a6Mat, Matrix.of_apply, Units.val_one, Module.End.one_apply, e7a6Vec_apply,
    Matrix.one_apply]

theorem e7a6Mat_mul {g h : ModGL Tag.E7 K} (_hg : g ∈ subsystemGroup Tag.E7 K e7a6support)
    (hh : h ∈ subsystemGroup Tag.E7 K e7a6support) :
    e7a6Mat (g * h) = e7a6Mat g * e7a6Mat h := by
  ext i j
  rw [e7a6Mat, Matrix.of_apply, Units.val_mul, Module.End.mul_apply, apply_e7a6Vec hh, map_sum,
    Finsupp.finsetSum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem e7a6Mat_xUnit {i₀ : Fin 7} (hi : e7Index i₀ ∈ e7a6support) {p q : Fin 7}
    (hpq : ∀ i j : Fin 7, e7a6Weight j + Pi.single (e7Index i₀) 1 = e7a6Weight i ↔
      (i = p ∧ j = q))
    (t : K) : e7a6Mat (xUnit Tag.E7 K (e7Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [e7a6Mat, Matrix.of_apply, coe_xUnit, xOp_e7a6Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_e7a6Label, e7a6Vec_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  have key := hpq i j
  by_cases h : e7a6Weight j + Pi.single (e7Index i₀) 1 = e7a6Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem e7a6Mat_yUnit {i₀ : Fin 7} (hi : e7Index i₀ ∈ e7a6support) {p q : Fin 7}
    (hpq : ∀ i j : Fin 7, e7a6Weight j - Pi.single (e7Index i₀) 1 = e7a6Weight i ↔
      (i = p ∧ j = q))
    (t : K) : e7a6Mat (yUnit Tag.E7 K (e7Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [e7a6Mat, Matrix.of_apply, coe_yUnit, yOp_e7a6Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_e7a6Label, e7a6Vec_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  have key := hpq i j
  by_cases h : e7a6Weight j - Pi.single (e7Index i₀) 1 = e7a6Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem e7a6Mat_x1 (t : K) : e7a6Mat (xUnit Tag.E7 K (e7Index 0) t) = 1 + single 0 1 t :=
  e7a6Mat_xUnit mem_e7a6support_0 (by decide +kernel) t

theorem e7a6Mat_y1 (t : K) : e7a6Mat (yUnit Tag.E7 K (e7Index 0) t) = 1 + single 1 0 t :=
  e7a6Mat_yUnit mem_e7a6support_0 (by decide +kernel) t

theorem e7a6Mat_x3 (t : K) : e7a6Mat (xUnit Tag.E7 K (e7Index 2) t) = 1 + single 1 2 t :=
  e7a6Mat_xUnit mem_e7a6support_2 (by decide +kernel) t

theorem e7a6Mat_y3 (t : K) : e7a6Mat (yUnit Tag.E7 K (e7Index 2) t) = 1 + single 2 1 t :=
  e7a6Mat_yUnit mem_e7a6support_2 (by decide +kernel) t

theorem e7a6Mat_x4 (t : K) : e7a6Mat (xUnit Tag.E7 K (e7Index 3) t) = 1 + single 2 3 t :=
  e7a6Mat_xUnit mem_e7a6support_3 (by decide +kernel) t

theorem e7a6Mat_y4 (t : K) : e7a6Mat (yUnit Tag.E7 K (e7Index 3) t) = 1 + single 3 2 t :=
  e7a6Mat_yUnit mem_e7a6support_3 (by decide +kernel) t

theorem e7a6Mat_x5 (t : K) : e7a6Mat (xUnit Tag.E7 K (e7Index 4) t) = 1 + single 3 4 t :=
  e7a6Mat_xUnit mem_e7a6support_4 (by decide +kernel) t

theorem e7a6Mat_y5 (t : K) : e7a6Mat (yUnit Tag.E7 K (e7Index 4) t) = 1 + single 4 3 t :=
  e7a6Mat_yUnit mem_e7a6support_4 (by decide +kernel) t

theorem e7a6Mat_x6 (t : K) : e7a6Mat (xUnit Tag.E7 K (e7Index 5) t) = 1 + single 4 5 t :=
  e7a6Mat_xUnit mem_e7a6support_5 (by decide +kernel) t

theorem e7a6Mat_y6 (t : K) : e7a6Mat (yUnit Tag.E7 K (e7Index 5) t) = 1 + single 5 4 t :=
  e7a6Mat_yUnit mem_e7a6support_5 (by decide +kernel) t

theorem e7a6Mat_x7 (t : K) : e7a6Mat (xUnit Tag.E7 K (e7Index 6) t) = 1 + single 5 6 t :=
  e7a6Mat_xUnit mem_e7a6support_6 (by decide +kernel) t

theorem e7a6Mat_y7 (t : K) : e7a6Mat (yUnit Tag.E7 K (e7Index 6) t) = 1 + single 6 5 t :=
  e7a6Mat_yUnit mem_e7a6support_6 (by decide +kernel) t

theorem e7a6Weight_pairing : ∀ k : Fin 7,
    (∑ j, Tag.E7.cartan (e7Index 0) j * e7a6Weight k j) = (![1, -1, 0, 0, 0, 0, 0] : Fin 7 → ℤ) k ∧
    (∑ j, Tag.E7.cartan (e7Index 2) j * e7a6Weight k j) = (![0, 1, -1, 0, 0, 0, 0] : Fin 7 → ℤ) k ∧
    (∑ j, Tag.E7.cartan (e7Index 3) j * e7a6Weight k j) = (![0, 0, 1, -1, 0, 0, 0] : Fin 7 → ℤ) k ∧
    (∑ j, Tag.E7.cartan (e7Index 4) j * e7a6Weight k j) = (![0, 0, 0, 1, -1, 0, 0] : Fin 7 → ℤ) k ∧
    (∑ j, Tag.E7.cartan (e7Index 5) j * e7a6Weight k j) = (![0, 0, 0, 0, 1, -1, 0] : Fin 7 → ℤ) k ∧
    (∑ j, Tag.E7.cartan (e7Index 6) j * e7a6Weight k j) = (![0, 0, 0, 0, 0, 1, -1] : Fin 7 → ℤ) k := by
  decide +kernel

theorem e7a6Mat_torusElt (i : Fin Tag.E7.rank) (a : Kˣ) :
    e7a6Mat (torusElt Tag.E7 K i a) = Matrix.diagonal fun k =>
      ((a ^ (∑ j, Tag.E7.cartan i j * e7a6Weight k j) : Kˣ) : K) := by
  ext p q
  rw [e7a6Mat, Matrix.of_apply, ← rootVec_e7a6Weight, torusElt_rootVec i a (isRoot_e7a6Weight q),
    rootVec_e7a6Weight, Finsupp.smul_apply, e7a6Vec_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

theorem torusElt_mem_e7a6Group {i : Fin Tag.E7.rank} (hi : i ∈ e7a6support) (a : Kˣ) :
    torusElt Tag.E7 K i a ∈ subsystemGroup Tag.E7 K e7a6support :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

@[expose] def e7a6TorusElt (a b c d e f : Kˣ) : ModGL Tag.E7 K :=
  torusElt Tag.E7 K (e7Index 0) a *
    torusElt Tag.E7 K (e7Index 2) b *
    torusElt Tag.E7 K (e7Index 3) c *
    torusElt Tag.E7 K (e7Index 4) d *
    torusElt Tag.E7 K (e7Index 5) e *
    torusElt Tag.E7 K (e7Index 6) f

theorem e7a6TorusElt_mem (a b c d e f : Kˣ) :
    e7a6TorusElt a b c d e f ∈ subsystemGroup Tag.E7 K e7a6support :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (torusElt_mem_e7a6Group mem_e7a6support_0 a)
    (torusElt_mem_e7a6Group mem_e7a6support_2 b))
    (torusElt_mem_e7a6Group mem_e7a6support_3 c))
    (torusElt_mem_e7a6Group mem_e7a6support_4 d))
    (torusElt_mem_e7a6Group mem_e7a6support_5 e))
    (torusElt_mem_e7a6Group mem_e7a6support_6 f)

theorem e7a6Mat_e7a6TorusElt (a b c d e f : Kˣ) :
    e7a6Mat (e7a6TorusElt a b c d e f) =
      Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ * c : Kˣ) : K), ((c⁻¹ * d : Kˣ) : K),
        ((d⁻¹ * e : Kˣ) : K), ((e⁻¹ * f : Kˣ) : K), ((f⁻¹ : Kˣ) : K)] := by
  have m0 := torusElt_mem_e7a6Group (K := K) mem_e7a6support_0 a
  have m1 := torusElt_mem_e7a6Group (K := K) mem_e7a6support_2 b
  have m2 := torusElt_mem_e7a6Group (K := K) mem_e7a6support_3 c
  have m3 := torusElt_mem_e7a6Group (K := K) mem_e7a6support_4 d
  have m4 := torusElt_mem_e7a6Group (K := K) mem_e7a6support_5 e
  have m5 := torusElt_mem_e7a6Group (K := K) mem_e7a6support_6 f
  rw [e7a6TorusElt, e7a6Mat_mul (mul_mem (mul_mem (mul_mem (mul_mem m0 m1) m2) m3) m4) m5,
    e7a6Mat_mul (mul_mem (mul_mem (mul_mem m0 m1) m2) m3) m4,
    e7a6Mat_mul (mul_mem (mul_mem m0 m1) m2) m3, e7a6Mat_mul (mul_mem m0 m1) m2,
    e7a6Mat_mul m0 m1, e7a6Mat_torusElt, e7a6Mat_torusElt, e7a6Mat_torusElt, e7a6Mat_torusElt,
    e7a6Mat_torusElt, e7a6Mat_torusElt, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := e7a6Weight_pairing k
  rw [h0, h1, h2, h3, h4, h5]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg]

theorem det_e7a6Mat {g : ModGL Tag.E7 K} (hg : g ∈ subsystemGroup Tag.E7 K e7a6support) :
    (e7a6Mat g).det = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_e7a6support i).1 hi with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e7a6Mat_x1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_x3]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_x4]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_x5]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_x6]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_x7]; exact det_transvection_of_ne _ _ (by decide) _
    · rcases (mem_e7a6support i).1 hi with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e7a6Mat_y1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_y3]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_y4]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_y5]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_y6]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e7a6Mat_y7]; exact det_transvection_of_ne _ _ (by decide) _
  | one => rw [e7a6Mat_one, det_one]
  | mul x y hx hy ihx ihy => rw [e7a6Mat_mul hx hy, det_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have h := e7a6Mat_mul (inv_mem hx) hx
    rw [inv_mul_cancel, e7a6Mat_one] at h
    have h' := congrArg Matrix.det h
    rw [det_one, det_mul, ih, mul_one] at h'
    exact h'.symm

variable (K) in
@[expose] def e7a6Rep : subsystemGroup Tag.E7 K e7a6support →* SL(7, K) where
  toFun g := ⟨e7a6Mat (g : ModGL Tag.E7 K), det_e7a6Mat g.2⟩
  map_one' := Subtype.ext e7a6Mat_one
  map_mul' g h := Subtype.ext (e7a6Mat_mul g.2 h.2)

theorem coe_e7a6Rep (g : subsystemGroup Tag.E7 K e7a6support) :
    ((e7a6Rep K g : SL(7, K)) : Matrix (Fin 7) (Fin 7) K) = e7a6Mat (g : ModGL Tag.E7 K) :=
  rfl

theorem e7a6Mat_inv {g : ModGL Tag.E7 K} (hg : g ∈ subsystemGroup Tag.E7 K e7a6support) :
    e7a6Mat g⁻¹ = (e7a6Mat g)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← e7a6Mat_mul hg (inv_mem hg), mul_inv_cancel, e7a6Mat_one]

theorem e7a6chainRoot_mem : ∀ k l : Fin 7, k ≠ l → ∃ m : Fin 126,
    e7RootVec m = chainRoot e7a6chain k l ∧
      ∀ i, ¬(i = e7Index 0 ∨ i = e7Index 2 ∨ i = e7Index 3 ∨ i = e7Index 4 ∨ i = e7Index 5 ∨ i = e7Index 6) →
        e7RootVec m i = 0 := by
  decide +kernel

theorem e7a6chainRoot_mem_parabolicRoots {k l : Fin 7} (hkl : k ≠ l) :
    chainRoot e7a6chain k l ∈ parabolicRoots Tag.E7 e7a6support := by
  obtain ⟨m, hm, hs⟩ := e7a6chainRoot_mem k l hkl
  rw [← hm]
  exact ⟨isRoot_e7RootVec m, fun i hi => hs i ((mem_e7a6support i).not.1 hi)⟩

theorem exists_e7a6chainRoot_of_support : ∀ m : Fin 126,
    (∀ i, ¬(i = e7Index 0 ∨ i = e7Index 2 ∨ i = e7Index 3 ∨ i = e7Index 4 ∨ i = e7Index 5 ∨ i = e7Index 6) →
      e7RootVec m i = 0) →
      ∃ k l : Fin 7, k ≠ l ∧ chainRoot e7a6chain k l = e7RootVec m := by
  decide +kernel

theorem exists_e7a6chainRoot_of_mem {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E7 e7a6support) :
    ∃ k l : Fin 7, k ≠ l ∧ chainRoot e7a6chain k l = α := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e7RootVec.1 hα.1
  exact exists_e7a6chainRoot_of_support m fun i hi => hα.2 i ((mem_e7a6support i).not.2 hi)

theorem pinnedX_mem_e7a6Group {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E7 e7a6support) (t : K) :
    pinnedX Tag.E7 K α t ∈ subsystemGroup Tag.E7 K e7a6support :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def E7A6RootFamily (i j : Fin 7) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
    e7a6Mat (pinnedX Tag.E7 K (chainRoot e7a6chain i j) t) = 1 + single i j ((ε : K) * t)

theorem e7a6RootFamily_of_eq {i j : Fin 7} {g : K → ModGL Tag.E7 K}
    (hg : ∀ t, pinnedX Tag.E7 K (chainRoot e7a6chain i j) t = g t)
    (h : ∀ t, e7a6Mat (g t) = 1 + single i j t) : E7A6RootFamily K i j :=
  ⟨1, Or.inl rfl, fun t => by rw [hg, h, Int.cast_one, one_mul]⟩

theorem e7a6chainRoot_triple : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
    (chainRoot e7a6chain i j + chainRoot e7a6chain j k = chainRoot e7a6chain i k ∧
      chainRoot e7a6chain i j ≠ chainRoot e7a6chain j k ∧
      chainRoot e7a6chain i j ≠ -chainRoot e7a6chain j k) := by
  decide +kernel

theorem e7a6RootFamily_comp {i j k : Fin 7} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h₁ : E7A6RootFamily K i j) (h₂ : E7A6RootFamily K j k) : E7A6RootFamily K i k := by
  obtain ⟨hsum, hne, hne'⟩ := e7a6chainRoot_triple i j k hij hik hjk
  obtain ⟨ε₁, hε₁, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, h₂⟩ := h₂
  have hα := e7a6chainRoot_mem_parabolicRoots hij
  have hβ := e7a6chainRoot_mem_parabolicRoots hjk
  have hγ := e7a6chainRoot_mem_parabolicRoots hik
  obtain ⟨hC, hcomm⟩ := (simply_laced_root_commutator_unit Tag.E7
    (Or.inr (Or.inr (Or.inl rfl))) hα.1 hβ.1 hne hne').1 (hsum ▸ hγ.1)
  set C := commConst Tag.E7 (chainRoot e7a6chain i j) (chainRoot e7a6chain j k) (1, 1)
  have hCC : (C : K) * C = 1 := by rcases hC with h | h <;> rw [h] <;> norm_num
  refine ⟨ε₁ * ε₂ * C, ?_, fun t => ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> rcases hC with h | h <;>
      simp [h]
  have e : pinnedX Tag.E7 K (chainRoot e7a6chain i k) t =
      ⁅pinnedX Tag.E7 K (chainRoot e7a6chain i j) 1,
        pinnedX Tag.E7 K (chainRoot e7a6chain j k) ((C : K) * t)⁆ := by
    rw [hcomm K 1 ((C : K) * t), hsum]
    congr 1
    rw [mul_one, ← mul_assoc, hCC, one_mul]
  have m1 := pinnedX_mem_e7a6Group hα (1 : K)
  have m2 := pinnedX_mem_e7a6Group hβ ((C : K) * t)
  rw [e, commutatorElement_def, e7a6Mat_mul (mul_mem (mul_mem m1 m2) (inv_mem m1)) (inv_mem m2),
    e7a6Mat_mul (mul_mem m1 m2) (inv_mem m1), e7a6Mat_mul m1 m2, e7a6Mat_inv m1, e7a6Mat_inv m2,
    h₁, h₂, CFSG.LinearGroups.elementary_three_index_commutator hik hij hjk.symm]
  congr 2
  push_cast
  ring

theorem e7a6chainRoot_values :
    chainRoot e7a6chain 0 1 = Pi.single (e7Index 0) 1 ∧
    chainRoot e7a6chain 1 2 = Pi.single (e7Index 2) 1 ∧
    chainRoot e7a6chain 2 3 = Pi.single (e7Index 3) 1 ∧
    chainRoot e7a6chain 3 4 = Pi.single (e7Index 4) 1 ∧
    chainRoot e7a6chain 4 5 = Pi.single (e7Index 5) 1 ∧
    chainRoot e7a6chain 5 6 = Pi.single (e7Index 6) 1 ∧
    chainRoot e7a6chain 1 0 = -Pi.single (e7Index 0) 1 ∧
    chainRoot e7a6chain 2 1 = -Pi.single (e7Index 2) 1 ∧
    chainRoot e7a6chain 3 2 = -Pi.single (e7Index 3) 1 ∧
    chainRoot e7a6chain 4 3 = -Pi.single (e7Index 4) 1 ∧
    chainRoot e7a6chain 5 4 = -Pi.single (e7Index 5) 1 ∧
    chainRoot e7a6chain 6 5 = -Pi.single (e7Index 6) 1 := by
  decide +kernel

theorem e7a6RootFamily_all : ∀ i j : Fin 7, i ≠ j → E7A6RootFamily K i j := by
  obtain ⟨c01, c12, c23, c34, c45, c56, c10, c21, c32, c43, c54, c65⟩ := e7a6chainRoot_values
  have f01 : E7A6RootFamily K 0 1 := e7a6RootFamily_of_eq
    (fun t => by rw [c01, pinnedX_single]) e7a6Mat_x1
  have f12 : E7A6RootFamily K 1 2 := e7a6RootFamily_of_eq
    (fun t => by rw [c12, pinnedX_single]) e7a6Mat_x3
  have f23 : E7A6RootFamily K 2 3 := e7a6RootFamily_of_eq
    (fun t => by rw [c23, pinnedX_single]) e7a6Mat_x4
  have f34 : E7A6RootFamily K 3 4 := e7a6RootFamily_of_eq
    (fun t => by rw [c34, pinnedX_single]) e7a6Mat_x5
  have f45 : E7A6RootFamily K 4 5 := e7a6RootFamily_of_eq
    (fun t => by rw [c45, pinnedX_single]) e7a6Mat_x6
  have f56 : E7A6RootFamily K 5 6 := e7a6RootFamily_of_eq
    (fun t => by rw [c56, pinnedX_single]) e7a6Mat_x7
  have f10 : E7A6RootFamily K 1 0 := e7a6RootFamily_of_eq
    (fun t => by rw [c10, pinnedX_neg_single]) e7a6Mat_y1
  have f21 : E7A6RootFamily K 2 1 := e7a6RootFamily_of_eq
    (fun t => by rw [c21, pinnedX_neg_single]) e7a6Mat_y3
  have f32 : E7A6RootFamily K 3 2 := e7a6RootFamily_of_eq
    (fun t => by rw [c32, pinnedX_neg_single]) e7a6Mat_y4
  have f43 : E7A6RootFamily K 4 3 := e7a6RootFamily_of_eq
    (fun t => by rw [c43, pinnedX_neg_single]) e7a6Mat_y5
  have f54 : E7A6RootFamily K 5 4 := e7a6RootFamily_of_eq
    (fun t => by rw [c54, pinnedX_neg_single]) e7a6Mat_y6
  have f65 : E7A6RootFamily K 6 5 := e7a6RootFamily_of_eq
    (fun t => by rw [c65, pinnedX_neg_single]) e7a6Mat_y7
  have f02 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f01 f12
  have f20 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f21 f10
  have f13 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f12 f23
  have f31 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f32 f21
  have f24 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f23 f34
  have f42 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f43 f32
  have f35 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f34 f45
  have f53 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f54 f43
  have f46 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f45 f56
  have f64 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f65 f54
  have f03 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f02 f23
  have f30 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f32 f20
  have f14 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f13 f34
  have f41 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f43 f31
  have f25 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f24 f45
  have f52 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f54 f42
  have f36 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f35 f56
  have f63 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f65 f53
  have f04 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f03 f34
  have f40 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f43 f30
  have f15 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f14 f45
  have f51 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f54 f41
  have f26 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f25 f56
  have f62 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f65 f52
  have f05 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f04 f45
  have f50 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f54 f40
  have f16 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f15 f56
  have f61 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f65 f51
  have f06 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f05 f56
  have f60 := e7a6RootFamily_comp (by decide) (by decide) (by decide) f65 f50
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f01
  | 0, 2, _ => exact f02
  | 0, 3, _ => exact f03
  | 0, 4, _ => exact f04
  | 0, 5, _ => exact f05
  | 0, 6, _ => exact f06
  | 1, 0, _ => exact f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f12
  | 1, 3, _ => exact f13
  | 1, 4, _ => exact f14
  | 1, 5, _ => exact f15
  | 1, 6, _ => exact f16
  | 2, 0, _ => exact f20
  | 2, 1, _ => exact f21
  | 2, 2, h => exact absurd rfl h
  | 2, 3, _ => exact f23
  | 2, 4, _ => exact f24
  | 2, 5, _ => exact f25
  | 2, 6, _ => exact f26
  | 3, 0, _ => exact f30
  | 3, 1, _ => exact f31
  | 3, 2, _ => exact f32
  | 3, 3, h => exact absurd rfl h
  | 3, 4, _ => exact f34
  | 3, 5, _ => exact f35
  | 3, 6, _ => exact f36
  | 4, 0, _ => exact f40
  | 4, 1, _ => exact f41
  | 4, 2, _ => exact f42
  | 4, 3, _ => exact f43
  | 4, 4, h => exact absurd rfl h
  | 4, 5, _ => exact f45
  | 4, 6, _ => exact f46
  | 5, 0, _ => exact f50
  | 5, 1, _ => exact f51
  | 5, 2, _ => exact f52
  | 5, 3, _ => exact f53
  | 5, 4, _ => exact f54
  | 5, 5, h => exact absurd rfl h
  | 5, 6, _ => exact f56
  | 6, 0, _ => exact f60
  | 6, 1, _ => exact f61
  | 6, 2, _ => exact f62
  | 6, 3, _ => exact f63
  | 6, 4, _ => exact f64
  | 6, 5, _ => exact f65
  | 6, 6, h => exact absurd rfl h

theorem e7a6Rep_surjective : Function.Surjective (e7a6Rep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, hε, h⟩ := e7a6RootFamily_all (K := K) i j hij
  have hmem := pinnedX_mem_e7a6Group (e7a6chainRoot_mem_parabolicRoots hij) ((ε : K) * c)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [coe_e7a6Rep, h, CFSG.LinearGroups.coe_transvection]
  congr 1
  rcases hε with rfl | rfl <;> simp

end CFSG.RankThree.PartOne.KE
