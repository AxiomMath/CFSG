module

public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2Data
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LinearAlgebra.LinearGroups.Generation

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix CFSG.RankThree.E6
open scoped commutatorElement

variable (K : Type) [Field K]

@[expose] def d4A2Vec (k : Fin 3) : RootModule Tag.D4 K := Finsupp.single (d4A2Label k) 1

theorem rootVec_d4A2Weight (k : Fin 3) : rootVec Tag.D4 K (d4A2Weight k) = d4A2Vec K k :=
  rootVec_eq_single_D4 (isRoot_d4A2Weight k)

variable {K}

theorem d4A2Vec_apply (k i : Fin 3) : d4A2Vec K k (d4A2Label i) = if i = k then 1 else 0 := by
  rw [d4A2Vec, Finsupp.single_apply]
  by_cases h : i = k
  · rw [ite_eq_left (congrArg d4A2Label h).symm, ite_eq_left h]
  · rw [ite_eq_right fun e => h (d4A2Label_injective e).symm, ite_eq_right h]

theorem rootVec_apply_d4A2Label (γ : Fin Tag.D4.rank → ℤ) (i : Fin 3) :
    rootVec Tag.D4 K γ (d4A2Label i) = if γ = d4A2Weight i then 1 else 0 := by
  by_cases hγ : IsRoot Tag.D4 γ
  · rw [rootVec_eq_single_D4 hγ, Finsupp.single_apply]
    by_cases h : γ = d4A2Weight i
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun e => h (congrArg Subtype.val (Sum.inr_injective e)), ite_eq_right h]
  · rw [rootVec_eq_zero_of_not_D4 hγ, Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact hγ (isRoot_d4A2Weight i)

variable (K) in
@[expose] def d4A2Module : Submodule K (RootModule Tag.D4 K) :=
  Submodule.span K (Set.range (d4A2Vec K))

theorem d4A2Vec_mem (k : Fin 3) : d4A2Vec K k ∈ d4A2Module K :=
  Submodule.subset_span ⟨k, rfl⟩

theorem eq_sum_of_mem_d4A2Module {m : RootModule Tag.D4 K} (hm : m ∈ d4A2Module K) :
    m = ∑ k, m (d4A2Label k) • d4A2Vec K k := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [d4A2Vec_apply, ite_eq_right hj, zero_smul])
      (by simp), d4A2Vec_apply, ite_eq_left rfl, one_smul]
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

theorem rootVec_mem_d4A2Module {γ : Fin Tag.D4.rank → ℤ}
    (h : (∀ m : Fin 24, d4RootVec m ≠ γ) ∨ ∃ k, d4A2Weight k = γ) :
    rootVec Tag.D4 K γ ∈ d4A2Module K := by
  rcases h with h | ⟨k, rfl⟩
  · have hγ : ¬IsRoot Tag.D4 γ := fun hγ => by
      obtain ⟨m, hm⟩ := isRoot_iff_exists_d4RootVec.1 hγ
      exact h m hm
    rw [rootVec_eq_zero_of_not_D4 hγ]
    exact zero_mem _
  · rw [rootVec_d4A2Weight]
    exact d4A2Vec_mem k

theorem xOp_d4A2Vec {i : Fin Tag.D4.rank} (hi : i ∈ d4SuppA2) (c : K) (k : Fin 3) :
    xOp Tag.D4 K i c (d4A2Vec K k) =
      d4A2Vec K k + c • rootVec Tag.D4 K (d4A2Weight k + Pi.single i 1) := by
  rw [← rootVec_d4A2Weight]
  exact xOp_rootVec_D4 i c (isRoot_d4A2Weight k)
    (d4A2Weight_ne_single k i ((mem_d4SuppA2 i).1 hi)).1
    (d4A2Weight_ne_single k i ((mem_d4SuppA2 i).1 hi)).2

theorem yOp_d4A2Vec {i : Fin Tag.D4.rank} (hi : i ∈ d4SuppA2) (c : K) (k : Fin 3) :
    yOp Tag.D4 K i c (d4A2Vec K k) =
      d4A2Vec K k + c • rootVec Tag.D4 K (d4A2Weight k - Pi.single i 1) := by
  rw [← rootVec_d4A2Weight]
  exact yOp_rootVec_D4 i c (isRoot_d4A2Weight k)
    (d4A2Weight_ne_single k i ((mem_d4SuppA2 i).1 hi)).1
    (d4A2Weight_ne_single k i ((mem_d4SuppA2 i).1 hi)).2

theorem mem_d4A2Module_of_mem {g : ModGL Tag.D4 K} (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2)
    {m : RootModule Tag.D4 K} (hm : m ∈ d4A2Module K) :
    (g : Module.End K (RootModule Tag.D4 K)) m ∈ d4A2Module K := by
  refine mem_of_mem_subsystemGroup' (fun i hi c v hv => ?_) (fun i hi c v hv => ?_) hg m hm
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [xOp_d4A2Vec hi]
      exact add_mem (d4A2Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_d4A2Module (d4A2Weight_add_single k i ((mem_d4SuppA2 i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [yOp_d4A2Vec hi]
      exact add_mem (d4A2Vec_mem k) (Submodule.smul_mem _ _
        (rootVec_mem_d4A2Module (d4A2Weight_sub_single k i ((mem_d4SuppA2 i).1 hi))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

@[expose] def d4A2Mat (g : ModGL Tag.D4 K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => (g : Module.End K (RootModule Tag.D4 K)) (d4A2Vec K j) (d4A2Label i)

theorem apply_d4A2Vec {g : ModGL Tag.D4 K} (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2)
    (j : Fin 3) :
    (g : Module.End K (RootModule Tag.D4 K)) (d4A2Vec K j) = ∑ i, d4A2Mat g i j • d4A2Vec K i :=
  eq_sum_of_mem_d4A2Module (mem_d4A2Module_of_mem hg (d4A2Vec_mem j))

theorem d4A2Mat_one : d4A2Mat (1 : ModGL Tag.D4 K) = 1 := by
  ext i j
  rw [d4A2Mat, Matrix.of_apply, Units.val_one, Module.End.one_apply, d4A2Vec_apply,
    Matrix.one_apply]

theorem d4A2Mat_mul {g h : ModGL Tag.D4 K} (hh : h ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    d4A2Mat (g * h) = d4A2Mat g * d4A2Mat h := by
  ext i j
  rw [d4A2Mat, Matrix.of_apply, Units.val_mul, Module.End.mul_apply, apply_d4A2Vec hh, map_sum,
    Finsupp.finsetSum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem d4A2Mat_xUnit {i : Fin Tag.D4.rank} (hi : i ∈ d4SuppA2) {p q : Fin 3}
    (hpq : ∀ a b : Fin 3, d4A2Weight b + Pi.single i 1 = d4A2Weight a ↔ (a = p ∧ b = q))
    (t : K) : d4A2Mat (xUnit Tag.D4 K i t) = 1 + single p q t := by
  ext a b
  rw [d4A2Mat, Matrix.of_apply, coe_xUnit, xOp_d4A2Vec hi, Finsupp.add_apply,
    Finsupp.smul_apply, rootVec_apply_d4A2Label, d4A2Vec_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  have key := hpq a b
  by_cases h : d4A2Weight b + Pi.single i 1 = d4A2Weight a
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = a ∧ q = b) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem d4A2Mat_yUnit {i : Fin Tag.D4.rank} (hi : i ∈ d4SuppA2) {p q : Fin 3}
    (hpq : ∀ a b : Fin 3, d4A2Weight b - Pi.single i 1 = d4A2Weight a ↔ (a = p ∧ b = q))
    (t : K) : d4A2Mat (yUnit Tag.D4 K i t) = 1 + single p q t := by
  ext a b
  rw [d4A2Mat, Matrix.of_apply, coe_yUnit, yOp_d4A2Vec hi, Finsupp.add_apply,
    Finsupp.smul_apply, rootVec_apply_d4A2Label, d4A2Vec_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  have key := hpq a b
  by_cases h : d4A2Weight b - Pi.single i 1 = d4A2Weight a
  · obtain ⟨rfl, rfl⟩ := key.1 h
    simp [h]
  · have h' : ¬(p = a ∧ q = b) := fun e => h (key.2 ⟨e.1.symm, e.2.symm⟩)
    simp [h, h']

theorem d4A2Mat_x0 (t : K) : d4A2Mat (xUnit Tag.D4 K 0 t) = 1 + single 0 1 t :=
  d4A2Mat_xUnit zero_mem_d4SuppA2 d4A2Weight_add_e0 t

theorem d4A2Mat_y0 (t : K) : d4A2Mat (yUnit Tag.D4 K 0 t) = 1 + single 1 0 t :=
  d4A2Mat_yUnit zero_mem_d4SuppA2 d4A2Weight_sub_e0 t

theorem d4A2Mat_x2 (t : K) : d4A2Mat (xUnit Tag.D4 K 2 t) = 1 + single 1 2 t :=
  d4A2Mat_xUnit two_mem_d4SuppA2 d4A2Weight_add_e2 t

theorem d4A2Mat_y2 (t : K) : d4A2Mat (yUnit Tag.D4 K 2 t) = 1 + single 2 1 t :=
  d4A2Mat_yUnit two_mem_d4SuppA2 d4A2Weight_sub_e2 t

theorem d4A2Mat_torusElt (i : Fin Tag.D4.rank) (a : Kˣ) :
    d4A2Mat (torusElt Tag.D4 K i a) = Matrix.diagonal fun k =>
      ((a ^ (∑ j, Tag.D4.cartan i j * d4A2Weight k j) : Kˣ) : K) := by
  ext p q
  rw [d4A2Mat, Matrix.of_apply, ← rootVec_d4A2Weight, torusElt_rootVec i a (isRoot_d4A2Weight q),
    rootVec_d4A2Weight, Finsupp.smul_apply, d4A2Vec_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

theorem torusElt_mem_d4A2Group {i : Fin Tag.D4.rank} (hi : i ∈ d4SuppA2) (a : Kˣ) :
    torusElt Tag.D4 K i a ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

@[expose] def d4A2TorusElt (t u : Kˣ) : ModGL Tag.D4 K :=
  torusElt Tag.D4 K 0 t * torusElt Tag.D4 K 2 u

theorem d4A2TorusElt_mem (t u : Kˣ) : d4A2TorusElt t u ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
  mul_mem (torusElt_mem_d4A2Group zero_mem_d4SuppA2 t) (torusElt_mem_d4A2Group two_mem_d4SuppA2 u)

theorem d4A2Mat_d4A2TorusElt (t u : Kˣ) :
    d4A2Mat (d4A2TorusElt t u) =
      Matrix.diagonal ![(t : K), ((t⁻¹ * u : Kˣ) : K), ((u⁻¹ : Kˣ) : K)] := by
  rw [d4A2TorusElt, d4A2Mat_mul (torusElt_mem_d4A2Group two_mem_d4SuppA2 u), d4A2Mat_torusElt,
    d4A2Mat_torusElt, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  obtain ⟨h0, h2⟩ := d4A2Weight_pairing k
  rw [h0, h2]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg]

theorem d4A2Mat_inv {g : ModGL Tag.D4 K} (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    d4A2Mat g⁻¹ = (d4A2Mat g)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← d4A2Mat_mul (inv_mem hg), mul_inv_cancel, d4A2Mat_one]

theorem det_d4A2Mat {g : ModGL Tag.D4 K} (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    (d4A2Mat g).det = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
      · rw [d4A2Mat_x0]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [d4A2Mat_x2]; exact det_transvection_of_ne _ _ (by decide) _
    · rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
      · rw [d4A2Mat_y0]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [d4A2Mat_y2]; exact det_transvection_of_ne _ _ (by decide) _
  | one => rw [d4A2Mat_one, det_one]
  | mul x y _ hy ihx ihy => rw [d4A2Mat_mul hy, det_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have h := d4A2Mat_mul (g := x⁻¹) hx
    rw [inv_mul_cancel, d4A2Mat_one] at h
    have h' := congrArg Matrix.det h
    rw [det_one, det_mul, ih, mul_one] at h'
    exact h'.symm

variable (K) in
@[expose] def d4A2Rep : subsystemGroup Tag.D4 K d4SuppA2 →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨d4A2Mat (g : ModGL Tag.D4 K), det_d4A2Mat g.2⟩
  map_one' := Subtype.ext d4A2Mat_one
  map_mul' _ h := Subtype.ext (d4A2Mat_mul h.2)

theorem coe_d4A2Rep (g : subsystemGroup Tag.D4 K d4SuppA2) :
    ((d4A2Rep K g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      d4A2Mat (g : ModGL Tag.D4 K) :=
  rfl

theorem pinnedX_mem_d4A2Group {α : Fin Tag.D4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.D4 d4SuppA2) (t : K) :
    pinnedX Tag.D4 K α t ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def D4A2RootFamily (i j : Fin 3) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
    d4A2Mat (pinnedX Tag.D4 K (chainRoot d4ChainA2 i j) t) = 1 + single i j ((ε : K) * t)

theorem d4A2RootFamily_of_eq {i j : Fin 3} {g : K → ModGL Tag.D4 K}
    (hg : ∀ t, pinnedX Tag.D4 K (chainRoot d4ChainA2 i j) t = g t)
    (h : ∀ t, d4A2Mat (g t) = 1 + single i j t) : D4A2RootFamily K i j :=
  ⟨1, Or.inl rfl, fun t => by rw [hg, h, Int.cast_one, one_mul]⟩

theorem d4A2RootFamily_comp {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsum : chainRoot d4ChainA2 i j + chainRoot d4ChainA2 j k = chainRoot d4ChainA2 i k)
    (hne : chainRoot d4ChainA2 i j ≠ chainRoot d4ChainA2 j k)
    (hne' : chainRoot d4ChainA2 i j ≠ -chainRoot d4ChainA2 j k)
    (h₁ : D4A2RootFamily K i j) (h₂ : D4A2RootFamily K j k) : D4A2RootFamily K i k := by
  obtain ⟨ε₁, hε₁, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, h₂⟩ := h₂
  have hα := chainRootA2_mem_parabolicRoots hij
  have hβ := chainRootA2_mem_parabolicRoots hjk
  have hγ := chainRootA2_mem_parabolicRoots hik
  obtain ⟨hC, hcomm⟩ := (simply_laced_root_commutator_unit Tag.D4 (Or.inl rfl) hα.1
    hβ.1 hne hne').1 (hsum ▸ hγ.1)
  set C := commConst Tag.D4 (chainRoot d4ChainA2 i j) (chainRoot d4ChainA2 j k) (1, 1)
  have hCC : (C : K) * C = 1 := by rcases hC with h | h <;> rw [h] <;> norm_num
  refine ⟨ε₁ * ε₂ * C, ?_, fun t => ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> rcases hC with h | h <;>
      simp [h]
  have e : pinnedX Tag.D4 K (chainRoot d4ChainA2 i k) t =
      ⁅pinnedX Tag.D4 K (chainRoot d4ChainA2 i j) 1,
        pinnedX Tag.D4 K (chainRoot d4ChainA2 j k) ((C : K) * t)⁆ := by
    rw [hcomm K 1 ((C : K) * t), hsum]
    congr 1
    rw [mul_one, ← mul_assoc, hCC, one_mul]
  have m1 := pinnedX_mem_d4A2Group hα (1 : K)
  have m2 := pinnedX_mem_d4A2Group hβ ((C : K) * t)
  rw [e, commutatorElement_def, d4A2Mat_mul (inv_mem m2), d4A2Mat_mul (inv_mem m1),
    d4A2Mat_mul m2, d4A2Mat_inv m1, d4A2Mat_inv m2, h₁, h₂,
    CFSG.LinearGroups.elementary_three_index_commutator hik hij hjk.symm]
  congr 2
  push_cast
  ring

theorem d4A2RootFamily_all : ∀ i j : Fin 3, i ≠ j → D4A2RootFamily K i j := by
  obtain ⟨c01, c12, c10, c21⟩ := chainRootA2_values
  obtain ⟨s02, s20⟩ := chainRootA2_sums
  have f01 : D4A2RootFamily K 0 1 :=
    d4A2RootFamily_of_eq (fun t => by rw [c01, pinnedX_single]) d4A2Mat_x0
  have f12 : D4A2RootFamily K 1 2 :=
    d4A2RootFamily_of_eq (fun t => by rw [c12, pinnedX_single]) d4A2Mat_x2
  have f10 : D4A2RootFamily K 1 0 :=
    d4A2RootFamily_of_eq (fun t => by rw [c10, pinnedX_neg_single]) d4A2Mat_y0
  have f21 : D4A2RootFamily K 2 1 :=
    d4A2RootFamily_of_eq (fun t => by rw [c21, pinnedX_neg_single]) d4A2Mat_y2
  have f02 :=
    d4A2RootFamily_comp (by decide) (by decide) (by decide) s02.1 s02.2.1 s02.2.2 f01 f12
  have f20 :=
    d4A2RootFamily_comp (by decide) (by decide) (by decide) s20.1 s20.2.1 s20.2.2 f21 f10
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f01
  | 0, 2, _ => exact f02
  | 1, 0, _ => exact f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f12
  | 2, 0, _ => exact f20
  | 2, 1, _ => exact f21
  | 2, 2, h => exact absurd rfl h

theorem d4A2Rep_surjective : Function.Surjective (d4A2Rep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, hε, h⟩ := d4A2RootFamily_all (K := K) i j hij
  have hmem := pinnedX_mem_d4A2Group (chainRootA2_mem_parabolicRoots hij) ((ε : K) * c)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [coe_d4A2Rep, h, CFSG.LinearGroups.coe_transvection]
  congr 1
  rcases hε with rfl | rfl <;> simp

theorem d4A2TorusElt_mul (t u t' u' : Kˣ) :
    d4A2TorusElt t u * d4A2TorusElt t' u' = d4A2TorusElt (t * t') (u * u') := by
  simp only [d4A2TorusElt, torusElt_mul]
  have h1 := torusElt_mul_comm (τ := Tag.D4) (R := K) 2 0 u t'
  calc torusElt Tag.D4 K 0 t * torusElt Tag.D4 K 2 u *
        (torusElt Tag.D4 K 0 t' * torusElt Tag.D4 K 2 u')
      = torusElt Tag.D4 K 0 t * (torusElt Tag.D4 K 2 u * torusElt Tag.D4 K 0 t') *
          torusElt Tag.D4 K 2 u' := by group
    _ = _ := by rw [h1]; group

theorem d4A2TorusElt_one : d4A2TorusElt (1 : Kˣ) 1 = 1 := by
  simp only [d4A2TorusElt, torusElt_one, mul_one]

theorem d4A2TorusElt_inv (t u : Kˣ) : (d4A2TorusElt t u)⁻¹ = d4A2TorusElt t⁻¹ u⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [d4A2TorusElt_mul, mul_inv_cancel, mul_inv_cancel, d4A2TorusElt_one]

theorem mem_subsystemTorus_d4A2 {g : ModGL Tag.D4 K} :
    g ∈ subsystemTorus Tag.D4 K d4SuppA2 ↔ ∃ t u : Kˣ, g = d4A2TorusElt t u := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, t, rfl⟩ := hx
      rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
      · exact ⟨t, 1, by simp only [d4A2TorusElt, torusElt_one, mul_one]⟩
      · exact ⟨1, t, by simp only [d4A2TorusElt, torusElt_one, one_mul]⟩
    | one => exact ⟨1, 1, d4A2TorusElt_one.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨t, u, rfl⟩ := hx
      obtain ⟨t', u', rfl⟩ := hy
      exact ⟨_, _, d4A2TorusElt_mul t u t' u'⟩
    | inv x _ hx =>
      obtain ⟨t, u, rfl⟩ := hx
      exact ⟨_, _, d4A2TorusElt_inv t u⟩
  · rintro ⟨t, u, rfl⟩
    exact mul_mem (torusElt_mem_subsystemTorus zero_mem_d4SuppA2 t)
      (torusElt_mem_subsystemTorus two_mem_d4SuppA2 u)

end CFSG.RankThree.Chevalley
