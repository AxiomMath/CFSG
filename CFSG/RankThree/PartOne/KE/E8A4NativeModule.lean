module

public import CFSG.RankThree.PartOne.KE.E8A2NativeModule

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped commutatorElement Pointwise MatrixGroups

@[expose] def e8a4support : Set (Fin Tag.E8.rank) :=
  {e8Index 0, e8Index 2, e8Index 3, e8Index 4}

theorem mem_e8a4support (i : Fin Tag.E8.rank) :
    i ∈ e8a4support ↔ (i = e8Index 0 ∨ i = e8Index 2 ∨ i = e8Index 3 ∨ i = e8Index 4) := by
  simp only [e8a4support, Set.mem_insert_iff, Set.mem_singleton_iff]

@[expose] def e8a4chain : Fin 4 → Fin Tag.E8.rank :=
  ![e8Index 0, e8Index 2, e8Index 3, e8Index 4]

theorem mem_e8a4support_0 : e8Index 0 ∈ e8a4support := (mem_e8a4support _).2 (Or.inl rfl)

theorem mem_e8a4support_2 : e8Index 2 ∈ e8a4support :=
  (mem_e8a4support _).2 (Or.inr (Or.inl rfl))

theorem mem_e8a4support_3 : e8Index 3 ∈ e8a4support :=
  (mem_e8a4support _).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem mem_e8a4support_4 : e8Index 4 ∈ e8a4support :=
  (mem_e8a4support _).2 (Or.inr (Or.inr (Or.inr rfl)))

@[expose] def e8a4Weight : Fin 5 → Fin Tag.E8.rank → ℤ :=
  (![![1, 0, 1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0]] : Fin 5 → Fin 8 → ℤ)

theorem exists_e8RootVec_e8a4Weight :
    ∀ k : Fin 5, ∃ m : Fin 240, e8RootVec m = e8a4Weight k := by
  decide +kernel

theorem isRoot_e8a4Weight (k : Fin 5) : IsRoot Tag.E8 (e8a4Weight k) := by
  obtain ⟨m, hm⟩ := exists_e8RootVec_e8a4Weight k
  rw [← hm]
  exact isRoot_e8RootVec m

theorem e8a4Weight_injective : Function.Injective e8a4Weight := by
  intro k k' h
  revert k k'
  decide +kernel

abbrev e8a4Label (k : Fin 5) : Label Tag.E8 := Sum.inr ⟨e8a4Weight k, isRoot_e8a4Weight k⟩

theorem e8a4Label_injective : Function.Injective e8a4Label := by
  intro k k' h
  exact e8a4Weight_injective (congrArg Subtype.val (Sum.inr_injective h))

variable (K : Type) [Field K]

@[expose] def e8a4Vec (k : Fin 5) : RootModule Tag.E8 K := Finsupp.single (e8a4Label k) 1

theorem rootVec_e8a4Weight (k : Fin 5) : rootVec Tag.E8 K (e8a4Weight k) = e8a4Vec K k :=
  CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K (isRoot_e8a4Weight k)

variable {K}

theorem e8a4Vec_apply (k i : Fin 5) : e8a4Vec K k (e8a4Label i) = if i = k then 1 else 0 := by
  rw [e8a4Vec, Finsupp.single_apply]
  by_cases h : i = k
  · rw [ite_eq_left (congrArg e8a4Label h).symm, ite_eq_left h]
  · rw [ite_eq_right fun e => h (e8a4Label_injective e).symm, ite_eq_right h]

theorem rootVec_apply_e8a4Label (γ : Fin Tag.E8.rank → ℤ) (i : Fin 5) :
    rootVec Tag.E8 K γ (e8a4Label i) = if γ = e8a4Weight i then 1 else 0 := by
  by_cases hγ : IsRoot Tag.E8 γ
  · rw [CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K hγ, Finsupp.single_apply]
    by_cases h : γ = e8a4Weight i
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [e8_rootVec_eq_zero_of_not_isRoot hγ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hγ (isRoot_e8a4Weight i)

variable (K) in
@[expose] def e8a4Module : Submodule K (RootModule Tag.E8 K) :=
  Submodule.span K (Set.range (e8a4Vec K))

theorem e8a4Vec_mem (k : Fin 5) : e8a4Vec K k ∈ e8a4Module K :=
  Submodule.subset_span ⟨k, rfl⟩

theorem eq_sum_of_mem_e8a4Module {m : RootModule Tag.E8 K} (hm : m ∈ e8a4Module K) :
    m = ∑ k, m (e8a4Label k) • e8a4Vec K k := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [e8a4Vec_apply, ite_eq_right hj, zero_smul])
      (by simp), e8a4Vec_apply, ite_eq_left rfl, one_smul]
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

theorem rootVec_mem_e8a4Module {γ : Fin Tag.E8.rank → ℤ}
    (h : (∀ m : Fin 240, e8RootVec m ≠ γ) ∨ ∃ k, e8a4Weight k = γ) :
    rootVec Tag.E8 K γ ∈ e8a4Module K := by
  rcases h with h | ⟨k, rfl⟩
  · have hγ : ¬IsRoot Tag.E8 γ := fun hγ => by
      obtain ⟨m, hm⟩ := isRoot_iff_exists_e8RootVec.1 hγ
      exact h m hm
    rw [e8_rootVec_eq_zero_of_not_isRoot hγ]
    exact zero_mem _
  · rw [rootVec_e8a4Weight]
    exact e8a4Vec_mem k

theorem e8a4Weight_ne_single : ∀ k : Fin 5, ∀ i : Fin 8, (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
    e8a4Weight k ≠ Pi.single (e8Index i) 1 ∧ e8a4Weight k ≠ -Pi.single (e8Index i) 1 := by
  decide +kernel

theorem e8a4Weight_add_single : ∀ k : Fin 5, ∀ i : Fin 8, (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
    (∀ m : Fin 240, e8RootVec m ≠ e8a4Weight k + Pi.single (e8Index i) 1) ∨
      ∃ k', e8a4Weight k' = e8a4Weight k + Pi.single (e8Index i) 1 := by
  decide +kernel

theorem e8a4Weight_sub_single : ∀ k : Fin 5, ∀ i : Fin 8, (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
    (∀ m : Fin 240, e8RootVec m ≠ e8a4Weight k - Pi.single (e8Index i) 1) ∨
      ∃ k', e8a4Weight k' = e8a4Weight k - Pi.single (e8Index i) 1 := by
  decide +kernel

theorem xOp_e8a4Vec {i : Fin Tag.E8.rank} (hi : i ∈ e8a4support) (c : K) (k : Fin 5) :
    xOp Tag.E8 K i c (e8a4Vec K k) =
      e8a4Vec K k + c • rootVec Tag.E8 K (e8a4Weight k + Pi.single i 1) := by
  rw [← rootVec_e8a4Weight]
  exact xOp_rootVec_E8 i c (isRoot_e8a4Weight k)
    (e8a4Weight_ne_single k i ((mem_e8a4support i).1 hi)).1
    (e8a4Weight_ne_single k i ((mem_e8a4support i).1 hi)).2

theorem yOp_e8a4Vec {i : Fin Tag.E8.rank} (hi : i ∈ e8a4support) (c : K) (k : Fin 5) :
    yOp Tag.E8 K i c (e8a4Vec K k) =
      e8a4Vec K k + c • rootVec Tag.E8 K (e8a4Weight k - Pi.single i 1) := by
  rw [← rootVec_e8a4Weight]
  exact yOp_rootVec_E8 i c (isRoot_e8a4Weight k)
    (e8a4Weight_ne_single k i ((mem_e8a4support i).1 hi)).1
    (e8a4Weight_ne_single k i ((mem_e8a4support i).1 hi)).2

theorem mem_e8a4Module_of_mem {g : ModGL Tag.E8 K}
    (hg : g ∈ subsystemGroup Tag.E8 K e8a4support)
    {m : RootModule Tag.E8 K} (hm : m ∈ e8a4Module K) :
    (g : Module.End K (RootModule Tag.E8 K)) m ∈ e8a4Module K := by
  refine mem_of_mem_subsystemGroup_of_invariant (fun i hi c v hv => ?_)
    (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [xOp_e8a4Vec hi]
      exact add_mem (e8a4Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_e8a4Module (e8a4Weight_add_single k i ((mem_e8a4support i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [yOp_e8a4Vec hi]
      exact add_mem (e8a4Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_e8a4Module (e8a4Weight_sub_single k i ((mem_e8a4support i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

@[expose] def e8a4Mat (g : ModGL Tag.E8 K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.of fun i j => (g : Module.End K (RootModule Tag.E8 K)) (e8a4Vec K j) (e8a4Label i)

theorem apply_e8a4Vec {g : ModGL Tag.E8 K} (hg : g ∈ subsystemGroup Tag.E8 K e8a4support)
    (j : Fin 5) :
    (g : Module.End K (RootModule Tag.E8 K)) (e8a4Vec K j) = ∑ i, e8a4Mat g i j • e8a4Vec K i :=
  eq_sum_of_mem_e8a4Module (mem_e8a4Module_of_mem hg (e8a4Vec_mem j))

theorem e8a4Mat_one : e8a4Mat (1 : ModGL Tag.E8 K) = 1 := by
  ext i j
  rw [e8a4Mat, Matrix.of_apply, Units.val_one, Module.End.one_apply, e8a4Vec_apply,
    Matrix.one_apply]

theorem e8a4Mat_mul {g h : ModGL Tag.E8 K} (_hg : g ∈ subsystemGroup Tag.E8 K e8a4support)
    (hh : h ∈ subsystemGroup Tag.E8 K e8a4support) :
    e8a4Mat (g * h) = e8a4Mat g * e8a4Mat h := by
  ext i j
  rw [e8a4Mat, Matrix.of_apply, Units.val_mul, Module.End.mul_apply, apply_e8a4Vec hh, map_sum,
    Finsupp.finsetSum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem e8a4Mat_xUnit {i₀ : Fin 8} (hi : e8Index i₀ ∈ e8a4support) {p q : Fin 5}
    (hpq : ∀ i j : Fin 5, e8a4Weight j + Pi.single (e8Index i₀) 1 = e8a4Weight i ↔
      (i = p ∧ j = q))
    (t : K) : e8a4Mat (xUnit Tag.E8 K (e8Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [e8a4Mat, Matrix.of_apply, coe_xUnit, xOp_e8a4Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_e8a4Label, e8a4Vec_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  have key := hpq i j
  by_cases h : e8a4Weight j + Pi.single (e8Index i₀) 1 = e8a4Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem e8a4Mat_yUnit {i₀ : Fin 8} (hi : e8Index i₀ ∈ e8a4support) {p q : Fin 5}
    (hpq : ∀ i j : Fin 5, e8a4Weight j - Pi.single (e8Index i₀) 1 = e8a4Weight i ↔
      (i = p ∧ j = q))
    (t : K) : e8a4Mat (yUnit Tag.E8 K (e8Index i₀) t) = 1 + single p q t := by
  ext i j
  rw [e8a4Mat, Matrix.of_apply, coe_yUnit, yOp_e8a4Vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    rootVec_apply_e8a4Label, e8a4Vec_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  have key := hpq i j
  by_cases h : e8a4Weight j - Pi.single (e8Index i₀) 1 = e8a4Weight i
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = i ∧ q = j) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem e8a4Mat_x1 (t : K) : e8a4Mat (xUnit Tag.E8 K (e8Index 0) t) = 1 + single 0 1 t :=
  e8a4Mat_xUnit mem_e8a4support_0 (by decide +kernel) t

theorem e8a4Mat_y1 (t : K) : e8a4Mat (yUnit Tag.E8 K (e8Index 0) t) = 1 + single 1 0 t :=
  e8a4Mat_yUnit mem_e8a4support_0 (by decide +kernel) t

theorem e8a4Mat_x3 (t : K) : e8a4Mat (xUnit Tag.E8 K (e8Index 2) t) = 1 + single 1 2 t :=
  e8a4Mat_xUnit mem_e8a4support_2 (by decide +kernel) t

theorem e8a4Mat_y3 (t : K) : e8a4Mat (yUnit Tag.E8 K (e8Index 2) t) = 1 + single 2 1 t :=
  e8a4Mat_yUnit mem_e8a4support_2 (by decide +kernel) t

theorem e8a4Mat_x4 (t : K) : e8a4Mat (xUnit Tag.E8 K (e8Index 3) t) = 1 + single 2 3 t :=
  e8a4Mat_xUnit mem_e8a4support_3 (by decide +kernel) t

theorem e8a4Mat_y4 (t : K) : e8a4Mat (yUnit Tag.E8 K (e8Index 3) t) = 1 + single 3 2 t :=
  e8a4Mat_yUnit mem_e8a4support_3 (by decide +kernel) t

theorem e8a4Mat_x5 (t : K) : e8a4Mat (xUnit Tag.E8 K (e8Index 4) t) = 1 + single 3 4 t :=
  e8a4Mat_xUnit mem_e8a4support_4 (by decide +kernel) t

theorem e8a4Mat_y5 (t : K) : e8a4Mat (yUnit Tag.E8 K (e8Index 4) t) = 1 + single 4 3 t :=
  e8a4Mat_yUnit mem_e8a4support_4 (by decide +kernel) t

theorem e8a4Weight_pairing : ∀ k : Fin 5,
    (∑ j, Tag.E8.cartan (e8Index 0) j * e8a4Weight k j) = (![1, -1, 0, 0, 0] : Fin 5 → ℤ) k ∧
    (∑ j, Tag.E8.cartan (e8Index 2) j * e8a4Weight k j) = (![0, 1, -1, 0, 0] : Fin 5 → ℤ) k ∧
    (∑ j, Tag.E8.cartan (e8Index 3) j * e8a4Weight k j) = (![0, 0, 1, -1, 0] : Fin 5 → ℤ) k ∧
    (∑ j, Tag.E8.cartan (e8Index 4) j * e8a4Weight k j) = (![0, 0, 0, 1, -1] : Fin 5 → ℤ) k := by
  decide +kernel

theorem e8a4Mat_torusElt (i : Fin Tag.E8.rank) (a : Kˣ) :
    e8a4Mat (torusElt Tag.E8 K i a) = Matrix.diagonal fun k =>
      ((a ^ (∑ j, Tag.E8.cartan i j * e8a4Weight k j) : Kˣ) : K) := by
  ext p q
  rw [e8a4Mat, Matrix.of_apply, ← rootVec_e8a4Weight, torusElt_rootVec i a (isRoot_e8a4Weight q),
    rootVec_e8a4Weight, Finsupp.smul_apply, e8a4Vec_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

theorem torusElt_mem_e8a4Group {i : Fin Tag.E8.rank} (hi : i ∈ e8a4support) (a : Kˣ) :
    torusElt Tag.E8 K i a ∈ subsystemGroup Tag.E8 K e8a4support :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

@[expose] def e8a4TorusElt (a b c d : Kˣ) : ModGL Tag.E8 K :=
  torusElt Tag.E8 K (e8Index 0) a * torusElt Tag.E8 K (e8Index 2) b *
    torusElt Tag.E8 K (e8Index 3) c * torusElt Tag.E8 K (e8Index 4) d

theorem e8a4TorusElt_mem (a b c d : Kˣ) :
    e8a4TorusElt a b c d ∈ subsystemGroup Tag.E8 K e8a4support :=
  mul_mem (mul_mem (mul_mem (torusElt_mem_e8a4Group mem_e8a4support_0 a)
    (torusElt_mem_e8a4Group mem_e8a4support_2 b)) (torusElt_mem_e8a4Group mem_e8a4support_3 c))
    (torusElt_mem_e8a4Group mem_e8a4support_4 d)

theorem e8a4Mat_e8a4TorusElt (a b c d : Kˣ) :
    e8a4Mat (e8a4TorusElt a b c d) =
      Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ * c : Kˣ) : K),
        ((c⁻¹ * d : Kˣ) : K), ((d⁻¹ : Kˣ) : K)] := by
  have m0 := torusElt_mem_e8a4Group (K := K) mem_e8a4support_0 a
  have m2 := torusElt_mem_e8a4Group (K := K) mem_e8a4support_2 b
  have m3 := torusElt_mem_e8a4Group (K := K) mem_e8a4support_3 c
  have m4 := torusElt_mem_e8a4Group (K := K) mem_e8a4support_4 d
  rw [e8a4TorusElt, e8a4Mat_mul (mul_mem (mul_mem m0 m2) m3) m4, e8a4Mat_mul (mul_mem m0 m2) m3,
    e8a4Mat_mul m0 m2, e8a4Mat_torusElt, e8a4Mat_torusElt, e8a4Mat_torusElt, e8a4Mat_torusElt,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  obtain ⟨h0, h2, h3, h4⟩ := e8a4Weight_pairing k
  rw [h0, h2, h3, h4]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg]

theorem det_e8a4Mat {g : ModGL Tag.E8 K} (hg : g ∈ subsystemGroup Tag.E8 K e8a4support) :
    (e8a4Mat g).det = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_e8a4support i).1 hi with rfl | rfl | rfl | rfl
      · rw [e8a4Mat_x1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e8a4Mat_x3]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e8a4Mat_x4]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e8a4Mat_x5]; exact det_transvection_of_ne _ _ (by decide) _
    · rcases (mem_e8a4support i).1 hi with rfl | rfl | rfl | rfl
      · rw [e8a4Mat_y1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e8a4Mat_y3]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e8a4Mat_y4]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [e8a4Mat_y5]; exact det_transvection_of_ne _ _ (by decide) _
  | one => rw [e8a4Mat_one, det_one]
  | mul x y hx hy ihx ihy => rw [e8a4Mat_mul hx hy, det_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have h := e8a4Mat_mul (inv_mem hx) hx
    rw [inv_mul_cancel, e8a4Mat_one] at h
    have h' := congrArg Matrix.det h
    rw [det_one, det_mul, ih, mul_one] at h'
    exact h'.symm

variable (K) in
@[expose] def e8a4Rep : subsystemGroup Tag.E8 K e8a4support →* SL(5, K) where
  toFun g := ⟨e8a4Mat (g : ModGL Tag.E8 K), det_e8a4Mat g.2⟩
  map_one' := Subtype.ext e8a4Mat_one
  map_mul' g h := Subtype.ext (e8a4Mat_mul g.2 h.2)

theorem coe_e8a4Rep (g : subsystemGroup Tag.E8 K e8a4support) :
    ((e8a4Rep K g : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = e8a4Mat (g : ModGL Tag.E8 K) :=
  rfl

theorem e8a4Mat_inv {g : ModGL Tag.E8 K} (hg : g ∈ subsystemGroup Tag.E8 K e8a4support) :
    e8a4Mat g⁻¹ = (e8a4Mat g)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← e8a4Mat_mul hg (inv_mem hg), mul_inv_cancel, e8a4Mat_one]

theorem e8a4chainRoot_mem : ∀ k l : Fin 5, k ≠ l → ∃ m : Fin 240,
    e8RootVec m = chainRoot e8a4chain k l ∧
      ∀ i, ¬(i = e8Index 0 ∨ i = e8Index 2 ∨ i = e8Index 3 ∨ i = e8Index 4) →
        e8RootVec m i = 0 := by
  decide +kernel

theorem e8a4chainRoot_mem_parabolicRoots {k l : Fin 5} (hkl : k ≠ l) :
    chainRoot e8a4chain k l ∈ parabolicRoots Tag.E8 e8a4support := by
  obtain ⟨m, hm, hs⟩ := e8a4chainRoot_mem k l hkl
  rw [← hm]
  exact ⟨isRoot_e8RootVec m, fun i hi => hs i ((mem_e8a4support i).not.1 hi)⟩

theorem exists_e8a4chainRoot_of_support : ∀ m : Fin 240,
    (∀ i, ¬(i = e8Index 0 ∨ i = e8Index 2 ∨ i = e8Index 3 ∨ i = e8Index 4) →
      e8RootVec m i = 0) →
      ∃ k l : Fin 5, k ≠ l ∧ chainRoot e8a4chain k l = e8RootVec m := by
  decide +kernel

theorem exists_e8a4chainRoot_of_mem {α : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E8 e8a4support) :
    ∃ k l : Fin 5, k ≠ l ∧ chainRoot e8a4chain k l = α := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα.1
  exact exists_e8a4chainRoot_of_support m fun i hi => hα.2 i ((mem_e8a4support i).not.2 hi)

theorem e8a4chainRoot_eq_sub :
    ∀ i j : Fin 5, chainRoot e8a4chain i j = e8a4Weight i - e8a4Weight j := by
  decide +kernel

theorem pinnedX_mem_e8a4Group {α : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E8 e8a4support) (t : K) :
    pinnedX Tag.E8 K α t ∈ subsystemGroup Tag.E8 K e8a4support :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def E8A4RootFamily (i j : Fin 5) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
    e8a4Mat (pinnedX Tag.E8 K (chainRoot e8a4chain i j) t) = 1 + single i j ((ε : K) * t)

theorem e8a4RootFamily_of_eq {i j : Fin 5} {g : K → ModGL Tag.E8 K}
    (hg : ∀ t, pinnedX Tag.E8 K (chainRoot e8a4chain i j) t = g t)
    (h : ∀ t, e8a4Mat (g t) = 1 + single i j t) : E8A4RootFamily K i j :=
  ⟨1, Or.inl rfl, fun t => by rw [hg, h, Int.cast_one, one_mul]⟩

theorem e8a4chainRoot_triple : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
    (chainRoot e8a4chain i j + chainRoot e8a4chain j k = chainRoot e8a4chain i k ∧
      chainRoot e8a4chain i j ≠ chainRoot e8a4chain j k ∧
      chainRoot e8a4chain i j ≠ -chainRoot e8a4chain j k) := by
  decide +kernel

theorem e8a4RootFamily_comp {i j k : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h₁ : E8A4RootFamily K i j) (h₂ : E8A4RootFamily K j k) : E8A4RootFamily K i k := by
  obtain ⟨hsum, hne, hne'⟩ := e8a4chainRoot_triple i j k hij hik hjk
  obtain ⟨ε₁, hε₁, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, h₂⟩ := h₂
  have hα := e8a4chainRoot_mem_parabolicRoots hij
  have hβ := e8a4chainRoot_mem_parabolicRoots hjk
  have hγ := e8a4chainRoot_mem_parabolicRoots hik
  obtain ⟨hC, hcomm⟩ := (simply_laced_root_commutator_unit Tag.E8
    (Or.inr (Or.inr (Or.inr rfl))) hα.1 hβ.1 hne hne').1 (hsum ▸ hγ.1)
  set C := commConst Tag.E8 (chainRoot e8a4chain i j) (chainRoot e8a4chain j k) (1, 1)
  have hCC : (C : K) * C = 1 := by rcases hC with h | h <;> rw [h] <;> norm_num
  refine ⟨ε₁ * ε₂ * C, ?_, fun t => ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> rcases hC with h | h <;>
      simp [h]
  have e : pinnedX Tag.E8 K (chainRoot e8a4chain i k) t =
      ⁅pinnedX Tag.E8 K (chainRoot e8a4chain i j) 1,
        pinnedX Tag.E8 K (chainRoot e8a4chain j k) ((C : K) * t)⁆ := by
    rw [hcomm K 1 ((C : K) * t), hsum]
    congr 1
    rw [mul_one, ← mul_assoc, hCC, one_mul]
  have m1 := pinnedX_mem_e8a4Group hα (1 : K)
  have m2 := pinnedX_mem_e8a4Group hβ ((C : K) * t)
  rw [e, commutatorElement_def, e8a4Mat_mul (mul_mem (mul_mem m1 m2) (inv_mem m1)) (inv_mem m2),
    e8a4Mat_mul (mul_mem m1 m2) (inv_mem m1), e8a4Mat_mul m1 m2, e8a4Mat_inv m1, e8a4Mat_inv m2,
    h₁, h₂, CFSG.LinearGroups.elementary_three_index_commutator hik hij hjk.symm]
  congr 2
  push_cast
  ring

theorem e8a4chainRoot_values :
    chainRoot e8a4chain 0 1 = Pi.single (e8Index 0) 1 ∧
    chainRoot e8a4chain 1 2 = Pi.single (e8Index 2) 1 ∧
    chainRoot e8a4chain 2 3 = Pi.single (e8Index 3) 1 ∧
    chainRoot e8a4chain 3 4 = Pi.single (e8Index 4) 1 ∧
    chainRoot e8a4chain 1 0 = -Pi.single (e8Index 0) 1 ∧
    chainRoot e8a4chain 2 1 = -Pi.single (e8Index 2) 1 ∧
    chainRoot e8a4chain 3 2 = -Pi.single (e8Index 3) 1 ∧
    chainRoot e8a4chain 4 3 = -Pi.single (e8Index 4) 1 := by
  decide +kernel

theorem e8a4RootFamily_all : ∀ i j : Fin 5, i ≠ j → E8A4RootFamily K i j := by
  obtain ⟨c01, c12, c23, c34, c10, c21, c32, c43⟩ := e8a4chainRoot_values
  have f01 : E8A4RootFamily K 0 1 := e8a4RootFamily_of_eq
    (fun t => by rw [c01, pinnedX_single]) e8a4Mat_x1
  have f12 : E8A4RootFamily K 1 2 := e8a4RootFamily_of_eq
    (fun t => by rw [c12, pinnedX_single]) e8a4Mat_x3
  have f23 : E8A4RootFamily K 2 3 := e8a4RootFamily_of_eq
    (fun t => by rw [c23, pinnedX_single]) e8a4Mat_x4
  have f34 : E8A4RootFamily K 3 4 := e8a4RootFamily_of_eq
    (fun t => by rw [c34, pinnedX_single]) e8a4Mat_x5
  have f10 : E8A4RootFamily K 1 0 := e8a4RootFamily_of_eq
    (fun t => by rw [c10, pinnedX_neg_single]) e8a4Mat_y1
  have f21 : E8A4RootFamily K 2 1 := e8a4RootFamily_of_eq
    (fun t => by rw [c21, pinnedX_neg_single]) e8a4Mat_y3
  have f32 : E8A4RootFamily K 3 2 := e8a4RootFamily_of_eq
    (fun t => by rw [c32, pinnedX_neg_single]) e8a4Mat_y4
  have f43 : E8A4RootFamily K 4 3 := e8a4RootFamily_of_eq
    (fun t => by rw [c43, pinnedX_neg_single]) e8a4Mat_y5
  have f02 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f01 f12
  have f13 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f12 f23
  have f24 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f23 f34
  have f20 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f21 f10
  have f31 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f32 f21
  have f42 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f43 f32
  have f03 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f02 f23
  have f14 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f13 f34
  have f30 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f32 f20
  have f41 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f43 f31
  have f04 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f03 f34
  have f40 := e8a4RootFamily_comp (by decide) (by decide) (by decide) f43 f30
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f01
  | 0, 2, _ => exact f02
  | 0, 3, _ => exact f03
  | 0, 4, _ => exact f04
  | 1, 0, _ => exact f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f12
  | 1, 3, _ => exact f13
  | 1, 4, _ => exact f14
  | 2, 0, _ => exact f20
  | 2, 1, _ => exact f21
  | 2, 2, h => exact absurd rfl h
  | 2, 3, _ => exact f23
  | 2, 4, _ => exact f24
  | 3, 0, _ => exact f30
  | 3, 1, _ => exact f31
  | 3, 2, _ => exact f32
  | 3, 3, h => exact absurd rfl h
  | 3, 4, _ => exact f34
  | 4, 0, _ => exact f40
  | 4, 1, _ => exact f41
  | 4, 2, _ => exact f42
  | 4, 3, _ => exact f43
  | 4, 4, h => exact absurd rfl h

theorem e8a4Rep_surjective : Function.Surjective (e8a4Rep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, hε, h⟩ := e8a4RootFamily_all (K := K) i j hij
  have hmem := pinnedX_mem_e8a4Group (e8a4chainRoot_mem_parabolicRoots hij) ((ε : K) * c)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [coe_e8a4Rep, h, CFSG.LinearGroups.coe_transvection]
  congr 1
  rcases hε with rfl | rfl <;> simp

end CFSG.RankThree.PartOne.KE
