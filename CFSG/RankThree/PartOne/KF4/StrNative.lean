module

public import CFSG.RankThree.PartOne.KE.E7A2NativeModule

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped Pointwise

structure StrNativeData (τ : Tag) (n : ℕ) (J : Set (Fin τ.rank))
    (w : Fin n → Fin τ.rank → ℤ) : Prop where
  isRoot : ∀ k, IsRoot τ (w k)
  injective : Function.Injective w
  ne_single : ∀ k, ∀ i ∈ J, w k ≠ Pi.single i 1 ∧ w k ≠ -Pi.single i 1
  up_mem : ∀ k, ∀ i ∈ J, ∀ j : ℕ, j ≤ stringUp τ i (w k) →
    ∃ k', w k' = w k + (j : ℤ) • Pi.single i 1
  down_mem : ∀ k, ∀ i ∈ J, ∀ j : ℕ, j ≤ stringDown τ i (w k) →
    ∃ k', w k' = w k - (j : ℤ) • Pi.single i 1

variable {τ : Tag} {n : ℕ} {J : Set (Fin τ.rank)} {w : Fin n → Fin τ.rank → ℤ}

namespace StrNativeData

variable (D : StrNativeData τ n J w)

abbrev label (k : Fin n) : Label τ := Sum.inr ⟨w k, D.isRoot k⟩

theorem label_injective : Function.Injective D.label := by
  intro k k' h
  exact D.injective (congrArg Subtype.val (Sum.inr_injective h))

variable (K : Type) [Field K]

@[expose] def vec (k : Fin n) : RootModule τ K := Finsupp.single (D.label k) 1

theorem rootVec_w (k : Fin n) : rootVec τ K (w k) = D.vec K k :=
  CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K (D.isRoot k)

@[expose] def module : Submodule K (RootModule τ K) := Submodule.span K (Set.range (D.vec K))

variable {K}

theorem vec_apply (k i : Fin n) : D.vec K k (D.label i) = if i = k then 1 else 0 := by
  rw [vec, Finsupp.single_apply]
  by_cases h : i = k
  · rw [ite_eq_left (congrArg D.label h).symm, ite_eq_left h]
  · rw [ite_eq_right fun e => h (D.label_injective e).symm, ite_eq_right h]

theorem rootVec_apply_label (γ : Fin τ.rank → ℤ) (i : Fin n) :
    rootVec τ K γ (D.label i) = if γ = w i then 1 else 0 := by
  by_cases hγ : IsRoot τ γ
  · rw [CFSG.TauCetiBridge.Minuscule.rootVec_eq_single K hγ, Finsupp.single_apply]
    by_cases h : γ = w i
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [rootVec, dite_eq_right hγ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hγ (D.isRoot i)

theorem vec_mem (k : Fin n) : D.vec K k ∈ D.module K := Submodule.subset_span ⟨k, rfl⟩

theorem eq_sum_of_mem_module {m : RootModule τ K} (hm : m ∈ D.module K) :
    m = ∑ k, m (D.label k) • D.vec K k := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [D.vec_apply, ite_eq_right hj, zero_smul])
      (by simp), D.vec_apply, ite_eq_left rfl, one_smul]
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


theorem xOp_vec {i : Fin τ.rank} (hi : i ∈ J) (c : K) (k : Fin n) :
    xOp τ K i c (D.vec K k) =
      ∑ j ∈ Finset.range (stringUp τ i (w k) + 1),
        (((stringDown τ i (w k) + j).choose j : K) * c ^ j) •
          rootVec τ K (w k + (j : ℤ) • Pi.single i 1) := by
  rw [← D.rootVec_w]
  exact CFSG.TauCetiBridge.Minuscule.xOp_rootVec_of_ne' K i c (D.isRoot k)
    (D.ne_single k i hi).1 (D.ne_single k i hi).2

theorem yOp_vec {i : Fin τ.rank} (hi : i ∈ J) (c : K) (k : Fin n) :
    yOp τ K i c (D.vec K k) =
      ∑ j ∈ Finset.range (stringDown τ i (w k) + 1),
        (((stringUp τ i (w k) + j).choose j : K) * c ^ j) •
          rootVec τ K (w k - (j : ℤ) • Pi.single i 1) := by
  rw [← D.rootVec_w]
  exact CFSG.TauCetiBridge.Minuscule.yOp_rootVec_of_ne' K i c (D.isRoot k)
    (D.ne_single k i hi).1 (D.ne_single k i hi).2

theorem mem_module_of_mem {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) {m : RootModule τ K}
    (hm : m ∈ D.module K) : (g : Module.End K (RootModule τ K)) m ∈ D.module K := by
  have hup : ∀ k, ∀ i ∈ J, ∀ j ∈ Finset.range (stringUp τ i (w k) + 1),
      rootVec τ K (w k + (j : ℤ) • Pi.single i 1) ∈ D.module K := by
    intro k i hi j hj
    obtain ⟨k', hk'⟩ := D.up_mem k i hi j (by simpa [Nat.lt_succ_iff] using hj)
    rw [← hk', D.rootVec_w]
    exact D.vec_mem k'
  have hdown : ∀ k, ∀ i ∈ J, ∀ j ∈ Finset.range (stringDown τ i (w k) + 1),
      rootVec τ K (w k - (j : ℤ) • Pi.single i 1) ∈ D.module K := by
    intro k i hi j hj
    obtain ⟨k', hk'⟩ := D.down_mem k i hi j (by simpa [Nat.lt_succ_iff] using hj)
    rw [← hk', D.rootVec_w]
    exact D.vec_mem k'
  refine KE.mem_of_mem_subsystemGroup_of_invariant (fun i hi c v hv => ?_)
    (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [D.xOp_vec hi]
      exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hup k i hi j hj)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [D.yOp_vec hi]
      exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hdown k i hi j hj)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem xOp_vec_eq {i : Fin τ.rank} (hi : i ∈ J) (c : K) (k : Fin n) (p q : ℕ)
    (hp : stringUp τ i (w k) = p) (hq : stringDown τ i (w k) = q) (a : Fin (p + 1) → Fin n)
    (ha : ∀ j : Fin (p + 1), w k + ((j : ℕ) : ℤ) • Pi.single i 1 = w (a j)) :
    xOp τ K i c (D.vec K k) =
      ∑ j : Fin (p + 1), ((((q + (j : ℕ)).choose j : ℕ) : K) * c ^ (j : ℕ)) • D.vec K (a j) := by
  rw [D.xOp_vec hi, hp, hq, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha j, D.rootVec_w]

theorem yOp_vec_eq {i : Fin τ.rank} (hi : i ∈ J) (c : K) (k : Fin n) (p q : ℕ)
    (hp : stringUp τ i (w k) = p) (hq : stringDown τ i (w k) = q) (a : Fin (q + 1) → Fin n)
    (ha : ∀ j : Fin (q + 1), w k - ((j : ℕ) : ℤ) • Pi.single i 1 = w (a j)) :
    yOp τ K i c (D.vec K k) =
      ∑ j : Fin (q + 1), ((((p + (j : ℕ)).choose j : ℕ) : K) * c ^ (j : ℕ)) • D.vec K (a j) := by
  rw [D.yOp_vec hi, hp, hq, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha j, D.rootVec_w]

@[expose] def Mat (g : ModGL τ K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (g : Module.End K (RootModule τ K)) (D.vec K j) (D.label i)

theorem Mat_eq_of_col {g : ModGL τ K} (X : Matrix (Fin n) (Fin n) K)
    (h : ∀ b, (g : Module.End K (RootModule τ K)) (D.vec K b) = ∑ a, X a b • D.vec K a) :
    D.Mat g = X := by
  ext a b
  rw [Mat, Matrix.of_apply, h b, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, D.vec_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem apply_vec {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) (j : Fin n) :
    (g : Module.End K (RootModule τ K)) (D.vec K j) = ∑ i, D.Mat g i j • D.vec K i :=
  D.eq_sum_of_mem_module (D.mem_module_of_mem hg (D.vec_mem j))

theorem Mat_one : D.Mat (1 : ModGL τ K) = 1 := by
  ext i j
  rw [Mat, Matrix.of_apply, Units.val_one, Module.End.one_apply, D.vec_apply, Matrix.one_apply]

theorem Mat_mul {g h : ModGL τ K} (_hg : g ∈ subsystemGroup τ K J)
    (hh : h ∈ subsystemGroup τ K J) : D.Mat (g * h) = D.Mat g * D.Mat h := by
  ext i j
  rw [Mat, Matrix.of_apply, Units.val_mul, Module.End.mul_apply, D.apply_vec hh, map_sum,
    Finsupp.finsetSum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem Mat_inv {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) : D.Mat g⁻¹ = (D.Mat g)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← D.Mat_mul hg (inv_mem hg), mul_inv_cancel, D.Mat_one]

theorem Mat_list_prod (l : List (ModGL τ K)) (hl : ∀ g ∈ l, g ∈ subsystemGroup τ K J) :
    D.Mat l.prod = (l.map D.Mat).prod := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil, D.Mat_one]
  | cons g l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      D.Mat_mul (hl g List.mem_cons_self) (Subgroup.list_prod_mem _ fun h hh => hl h
        (List.mem_cons_of_mem g hh)), ih fun h hh => hl h (List.mem_cons_of_mem g hh)]

theorem Mat_xUnit_apply {i : Fin τ.rank} (hi : i ∈ J) (t : K) (a b : Fin n) :
    D.Mat (xUnit τ K i t) a b =
      ∑ j ∈ Finset.range (stringUp τ i (w b) + 1),
        (((stringDown τ i (w b) + j).choose j : K) * t ^ j) *
          (if w b + (j : ℤ) • Pi.single i 1 = w a then 1 else 0) := by
  rw [Mat, Matrix.of_apply, coe_xUnit, D.xOp_vec hi, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, D.rootVec_apply_label, smul_eq_mul]

theorem Mat_yUnit_apply {i : Fin τ.rank} (hi : i ∈ J) (t : K) (a b : Fin n) :
    D.Mat (yUnit τ K i t) a b =
      ∑ j ∈ Finset.range (stringDown τ i (w b) + 1),
        (((stringUp τ i (w b) + j).choose j : K) * t ^ j) *
          (if w b - (j : ℤ) • Pi.single i 1 = w a then 1 else 0) := by
  rw [Mat, Matrix.of_apply, coe_yUnit, D.yOp_vec hi, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, D.rootVec_apply_label, smul_eq_mul]

theorem Mat_torusElt (i : Fin τ.rank) (a : Kˣ) :
    D.Mat (torusElt τ K i a) = Matrix.diagonal fun k =>
      ((a ^ (∑ j, τ.cartan i j * w k j) : Kˣ) : K) := by
  ext p q
  rw [Mat, Matrix.of_apply, ← D.rootVec_w, torusElt_rootVec i a (D.isRoot q), D.rootVec_w,
    Finsupp.smul_apply, D.vec_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

end StrNativeData

end CFSG.RankThree.PartOne.KF4
