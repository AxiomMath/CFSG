module

public import CFSG.RankThree.PartOne.KF4.Strings
public import CFSG.RankThree.PartOne.KE.E7A2NativeModule

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped Pointwise

structure MinNativeData (τ : Tag) (n : ℕ) (J : Set (Fin τ.rank))
    (w : Fin n → Fin τ.rank → ℤ) : Prop where
  isRoot : ∀ k, IsRoot τ (w k)
  injective : Function.Injective w
  ne_single : ∀ k, ∀ i ∈ J, w k ≠ Pi.single i 1 ∧ w k ≠ -Pi.single i 1
  not_both : ∀ k, ∀ i ∈ J, ¬(IsRoot τ (w k + Pi.single i 1) ∧ IsRoot τ (w k - Pi.single i 1))
  no_two_up : ∀ k, ∀ i ∈ J, ¬IsRoot τ (w k + (2 : ℤ) • Pi.single i 1)
  no_two_down : ∀ k, ∀ i ∈ J, ¬IsRoot τ (w k - (2 : ℤ) • Pi.single i 1)
  up_mem : ∀ k, ∀ i ∈ J, IsRoot τ (w k + Pi.single i 1) → ∃ k', w k' = w k + Pi.single i 1
  down_mem : ∀ k, ∀ i ∈ J, IsRoot τ (w k - Pi.single i 1) → ∃ k', w k' = w k - Pi.single i 1

@[expose] def nPlus {τ : Tag} {n : ℕ} (w : Fin n → Fin τ.rank → ℤ) (K : Type) [Field K]
    (i : Fin τ.rank) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b => if w b + Pi.single i 1 = w a then 1 else 0

@[expose] def nMinus {τ : Tag} {n : ℕ} (w : Fin n → Fin τ.rank → ℤ) (K : Type) [Field K]
    (i : Fin τ.rank) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b => if w b - Pi.single i 1 = w a then 1 else 0

variable {τ : Tag} {n : ℕ} {J : Set (Fin τ.rank)} {w : Fin n → Fin τ.rank → ℤ}

namespace MinNativeData

variable (D : MinNativeData τ n J w)

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

variable (K) in
omit D in
theorem rootVec_eq_zero_of_not_isRoot {β : Fin τ.rank → ℤ} (hβ : ¬IsRoot τ β) :
    rootVec τ K β = 0 := by
  rw [rootVec, dite_eq_right hβ]

theorem rootVec_mem_module {γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ γ ∨ ∃ k, w k = γ) :
    rootVec τ K γ ∈ D.module K := by
  rcases h with h | ⟨k, rfl⟩
  · rw [rootVec_eq_zero_of_not_isRoot K h]
    exact zero_mem _
  · rw [D.rootVec_w]
    exact D.vec_mem k


theorem xOp_vec {i : Fin τ.rank} (hi : i ∈ J) (c : K) (k : Fin n) :
    xOp τ K i c (D.vec K k) = D.vec K k + c • rootVec τ K (w k + Pi.single i 1) := by
  rw [← D.rootVec_w]
  exact xOp_rootVec_of_short_string K i c (D.isRoot k) (D.ne_single k i hi).1
    (D.ne_single k i hi).2 (D.not_both k i hi) (D.no_two_up k i hi)

theorem yOp_vec {i : Fin τ.rank} (hi : i ∈ J) (c : K) (k : Fin n) :
    yOp τ K i c (D.vec K k) = D.vec K k + c • rootVec τ K (w k - Pi.single i 1) := by
  rw [← D.rootVec_w]
  exact yOp_rootVec_of_short_string K i c (D.isRoot k) (D.ne_single k i hi).1
    (D.ne_single k i hi).2 (D.not_both k i hi) (D.no_two_down k i hi)

theorem mem_module_of_mem {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) {m : RootModule τ K}
    (hm : m ∈ D.module K) : (g : Module.End K (RootModule τ K)) m ∈ D.module K := by
  have hup : ∀ k, ∀ i ∈ J, rootVec τ K (w k + Pi.single i 1) ∈ D.module K := fun k i hi => by
    refine D.rootVec_mem_module ?_
    by_cases h : IsRoot τ (w k + Pi.single i 1)
    · exact Or.inr (D.up_mem k i hi h)
    · exact Or.inl h
  have hdown : ∀ k, ∀ i ∈ J, rootVec τ K (w k - Pi.single i 1) ∈ D.module K := fun k i hi => by
    refine D.rootVec_mem_module ?_
    by_cases h : IsRoot τ (w k - Pi.single i 1)
    · exact Or.inr (D.down_mem k i hi h)
    · exact Or.inl h
  refine KE.mem_of_mem_subsystemGroup_of_invariant (fun i hi c v hv => ?_)
    (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [D.xOp_vec hi]
      exact add_mem (D.vec_mem k) (Submodule.smul_mem _ _ (hup k i hi))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [D.yOp_vec hi]
      exact add_mem (D.vec_mem k) (Submodule.smul_mem _ _ (hdown k i hi))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

@[expose] def Mat (g : ModGL τ K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (g : Module.End K (RootModule τ K)) (D.vec K j) (D.label i)

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

theorem Mat_xUnit {i : Fin τ.rank} (hi : i ∈ J) (t : K) :
    D.Mat (xUnit τ K i t) = 1 + t • nPlus w K i := by
  ext a b
  rw [Mat, Matrix.of_apply, coe_xUnit, D.xOp_vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    D.rootVec_apply_label, D.vec_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    nPlus, Matrix.of_apply, smul_eq_mul]

theorem Mat_yUnit {i : Fin τ.rank} (hi : i ∈ J) (t : K) :
    D.Mat (yUnit τ K i t) = 1 + t • nMinus w K i := by
  ext a b
  rw [Mat, Matrix.of_apply, coe_yUnit, D.yOp_vec hi, Finsupp.add_apply, Finsupp.smul_apply,
    D.rootVec_apply_label, D.vec_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    nMinus, Matrix.of_apply, smul_eq_mul]

theorem Mat_xUnit_single {i : Fin τ.rank} (hi : i ∈ J) {p q : Fin n}
    (hpq : ∀ a b : Fin n, w b + Pi.single i 1 = w a ↔ (a = p ∧ b = q)) (t : K) :
    D.Mat (xUnit τ K i t) = 1 + Matrix.single p q t := by
  rw [D.Mat_xUnit hi]
  congr 1
  ext a b
  rw [Matrix.smul_apply, nPlus, Matrix.of_apply, Matrix.single_apply]
  by_cases h : w b + Pi.single i 1 = w a
  · obtain ⟨rfl, rfl⟩ := (hpq a b).1 h
    simp [h]
  · have h' : ¬(p = a ∧ q = b) := fun e => h ((hpq a b).2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem Mat_yUnit_single {i : Fin τ.rank} (hi : i ∈ J) {p q : Fin n}
    (hpq : ∀ a b : Fin n, w b - Pi.single i 1 = w a ↔ (a = p ∧ b = q)) (t : K) :
    D.Mat (yUnit τ K i t) = 1 + Matrix.single p q t := by
  rw [D.Mat_yUnit hi]
  congr 1
  ext a b
  rw [Matrix.smul_apply, nMinus, Matrix.of_apply, Matrix.single_apply]
  by_cases h : w b - Pi.single i 1 = w a
  · obtain ⟨rfl, rfl⟩ := (hpq a b).1 h
    simp [h]
  · have h' : ¬(p = a ∧ q = b) := fun e => h ((hpq a b).2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

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

end MinNativeData

end CFSG.RankThree.PartOne.KF4
