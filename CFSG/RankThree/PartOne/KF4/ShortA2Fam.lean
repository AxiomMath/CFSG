module

public import CFSG.RankThree.PartOne.KF4.ShortA2Rep

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups

section Fam

variable
  {K : Type} [Field K]

@[expose] def f4ShortRepFun (g : subsystemGroup Tag.F4 K f4ShortSupport) : SL(3, K) :=
  Classical.choose (exists_symRep g.2)

theorem Mat_f4ShortRepFun (g : subsystemGroup Tag.F4 K f4ShortSupport) :
    f4Short_data.Mat (g : ModGL Tag.F4 K) = symRep K (f4ShortRepFun g) :=
  Classical.choose_spec (exists_symRep g.2)

variable (K) in
@[expose] def f4ShortRep : subsystemGroup Tag.F4 K f4ShortSupport →* SL(3, K) where
  toFun := f4ShortRepFun
  map_one' := by
    apply symRep_injective
    rw [← Mat_f4ShortRepFun, map_one]
    exact f4Short_data.Mat_one
  map_mul' g h := by
    apply symRep_injective
    rw [map_mul, ← Mat_f4ShortRepFun, ← Mat_f4ShortRepFun, ← Mat_f4ShortRepFun]
    exact f4Short_data.Mat_mul g.2 h.2

theorem Mat_f4ShortRep (g : subsystemGroup Tag.F4 K f4ShortSupport) :
    f4Short_data.Mat (g : ModGL Tag.F4 K) = symRep K (f4ShortRep K g) :=
  Mat_f4ShortRepFun g

theorem f4ShortSigma_mem_parabolicRoots {k l : Fin 3} (hkl : k ≠ l) :
    f4ShortSigma k l ∈ parabolicRoots Tag.F4 f4ShortSupport := by
  obtain ⟨m, hm, hs⟩ := f4ShortSigma_mem k l hkl
  rw [← hm]
  exact ⟨isRoot_f4RootVec m, fun i hi => hs i ((mem_f4ShortSupport i).not.1 hi)⟩

theorem exists_f4ShortSigma_of_mem {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.F4 f4ShortSupport) :
    ∃ k l : Fin 3, k ≠ l ∧ f4ShortSigma k l = α := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hα.1
  exact exists_f4ShortSigma_of_support m fun i hi => hα.2 i ((mem_f4ShortSupport i).not.2 hi)

theorem pinnedX_mem_f4Short {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.F4 f4ShortSupport) (t : K) :
    pinnedX Tag.F4 K α t ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def F4ShortRootFamily (i j : Fin 3) (hij : i ≠ j) : Prop :=
  ∃ ε : Kˣ, ∀ t : K, f4Short_data.Mat (pinnedX Tag.F4 K (f4ShortSigma i j) t) =
    symRep K (Matrix.SpecialLinearGroup.transvection hij ((ε : K) * t))

theorem f4ShortRootFamily_of_eq {i j : Fin 3} (hij : i ≠ j) {g : K → ModGL Tag.F4 K}
    (hg : ∀ t, pinnedX Tag.F4 K (f4ShortSigma i j) t = g t)
    (h : ∀ t, f4Short_data.Mat (g t) =
      symRep K (Matrix.SpecialLinearGroup.transvection hij (-t))) : F4ShortRootFamily K i j hij :=
  ⟨-1, fun t => by rw [hg, h]; simp⟩

variable (K) in
@[expose] def f4ShortN : SL(3, K) :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-1) *
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-1)

theorem f4ShortN_conj_21 (c : K) :
    f4ShortN K * Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c *
        (f4ShortN K)⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  simp only [f4ShortN, Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.add_apply,
    Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem f4ShortN_conj_12 (c : K) :
    f4ShortN K * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c *
        (f4ShortN K)⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  simp only [f4ShortN, Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.add_apply,
    Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem Mat_f4Short_n3 :
    f4Short_data.Mat (weylElt Tag.F4 K (f4Index 2) 1) = symRep K (f4ShortN K) := by
  have h1 : weylElt Tag.F4 K (f4Index 2) 1 =
      xUnit Tag.F4 K (f4Index 2) 1 * yUnit Tag.F4 K (f4Index 2) (-1) *
        xUnit Tag.F4 K (f4Index 2) 1 := by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    simp
  have hx := xUnit_mem_subsystemGroup (τ := Tag.F4) (K := K)
    ((mem_f4ShortSupport _).2 (Or.inl rfl)) 1
  have hy := yUnit_mem_subsystemGroup (τ := Tag.F4) (K := K)
    ((mem_f4ShortSupport _).2 (Or.inl rfl)) (-1)
  rw [h1, f4Short_data.Mat_mul (mul_mem hx hy) hx, f4Short_data.Mat_mul hx hy, f4Short_Mat_x3,
    f4Short_Mat_y3, f4ShortX3_eq, f4ShortY3_eq, symCong_elem (K := K) 1 0 (by decide),
    symCong_elem (K := K) 0 1 (by decide), f4ShortN]
  simp only [map_mul, neg_neg]

theorem Mat_f4Short_n3_inv :
    f4Short_data.Mat (weylElt Tag.F4 K (f4Index 2) 1)⁻¹ = symRep K (f4ShortN K)⁻¹ := by
  have hn : weylElt Tag.F4 K (f4Index 2) 1 ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
    weylElt_mem_subsystemGroup ((mem_f4ShortSupport _).2 (Or.inl rfl)) 1
  rw [f4Short_data.Mat_inv hn, Mat_f4Short_n3]
  refine Matrix.inv_eq_right_inv ?_
  rw [← map_mul, mul_inv_cancel, map_one]

theorem Mat_pinnedX_simple_short :
    (∀ t : K, f4Short_data.Mat (pinnedX Tag.F4 K (f4ShortSigma 1 0) t) =
      symRep K (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-t))) ∧
    (∀ t : K, f4Short_data.Mat (pinnedX Tag.F4 K (f4ShortSigma 0 1) t) =
      symRep K (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (-t))) ∧
    (∀ t : K, f4Short_data.Mat (pinnedX Tag.F4 K (f4ShortSigma 2 1) t) =
      symRep K (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (-t))) ∧
    (∀ t : K, f4Short_data.Mat (pinnedX Tag.F4 K (f4ShortSigma 1 2) t) =
      symRep K (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (-t))) := by
  obtain ⟨c10, c21, c01, c12⟩ := f4ShortSigma_values
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [c10, pinnedX_single, f4Short_Mat_x3, f4ShortX3_eq, symCong_elem (K := K) 1 0 (by decide)]
  · rw [c01, pinnedX_neg_single, f4Short_Mat_y3, f4ShortY3_eq,
      symCong_elem (K := K) 0 1 (by decide)]
  · rw [c21, pinnedX_single, f4Short_Mat_x4, f4ShortX4_eq, symCong_elem (K := K) 2 1 (by decide)]
  · rw [c12, pinnedX_neg_single, f4Short_Mat_y4, f4ShortY4_eq,
      symCong_elem (K := K) 1 2 (by decide)]

theorem f4ShortRootFamily_20 : F4ShortRootFamily K 2 0 (by decide) := by
  obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4Index 2)
    (isRoot_single Tag.F4 (f4Index 3))
  have hs : f4ShortSigma 2 1 = Pi.single (f4Index 3) 1 := f4ShortSigma_values.2.1
  have hr := f4ShortSigma_reflect.1
  rw [← hs, hr] at h
  have hn : weylElt Tag.F4 K (f4Index 2) 1 ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
    weylElt_mem_subsystemGroup ((mem_f4ShortSupport _).2 (Or.inl rfl)) 1
  have hα : f4ShortSigma 2 1 ∈ parabolicRoots Tag.F4 f4ShortSupport :=
    f4ShortSigma_mem_parabolicRoots (by decide)
  refine ⟨Units.mkOfMulEqOne (-ε) (-ε) (by rw [neg_mul_neg]; exact hεε), fun t => ?_⟩
  have e : pinnedX Tag.F4 K (f4ShortSigma 2 0) t =
      weylElt Tag.F4 K (f4Index 2) 1 * pinnedX Tag.F4 K (f4ShortSigma 2 1) (ε * t) *
        (weylElt Tag.F4 K (f4Index 2) 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := pinnedX_mem_f4Short hα (ε * t)
  rw [e, f4Short_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Short_data.Mat_mul hn hX,
    Mat_f4Short_n3, Mat_f4Short_n3_inv, Mat_pinnedX_simple_short.2.2.1, ← map_mul, ← map_mul,
    f4ShortN_conj_21]
  congr 2
  simp

theorem f4ShortRootFamily_02 : F4ShortRootFamily K 0 2 (by decide) := by
  obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4Index 2)
    (isRoot_neg_single Tag.F4 (f4Index 3))
  have hs : f4ShortSigma 1 2 = -Pi.single (f4Index 3) 1 := f4ShortSigma_values.2.2.2
  have hr := f4ShortSigma_reflect.2
  rw [← hs, hr] at h
  have hn : weylElt Tag.F4 K (f4Index 2) 1 ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
    weylElt_mem_subsystemGroup ((mem_f4ShortSupport _).2 (Or.inl rfl)) 1
  have hα : f4ShortSigma 1 2 ∈ parabolicRoots Tag.F4 f4ShortSupport :=
    f4ShortSigma_mem_parabolicRoots (by decide)
  refine ⟨Units.mkOfMulEqOne (-ε) (-ε) (by rw [neg_mul_neg]; exact hεε), fun t => ?_⟩
  have e : pinnedX Tag.F4 K (f4ShortSigma 0 2) t =
      weylElt Tag.F4 K (f4Index 2) 1 * pinnedX Tag.F4 K (f4ShortSigma 1 2) (ε * t) *
        (weylElt Tag.F4 K (f4Index 2) 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := pinnedX_mem_f4Short hα (ε * t)
  rw [e, f4Short_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Short_data.Mat_mul hn hX,
    Mat_f4Short_n3, Mat_f4Short_n3_inv, Mat_pinnedX_simple_short.2.2.2, ← map_mul, ← map_mul,
    f4ShortN_conj_12]
  congr 2
  simp

theorem f4ShortRootFamily_all : ∀ (i j : Fin 3) (hij : i ≠ j), F4ShortRootFamily K i j hij := by
  obtain ⟨f10, f01, f21, f12⟩ := Mat_pinnedX_simple_short (K := K)
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f4ShortRootFamily_of_eq (by decide) (fun t => rfl) f01
  | 0, 2, _ => exact f4ShortRootFamily_02
  | 1, 0, _ => exact f4ShortRootFamily_of_eq (by decide) (fun t => rfl) f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f4ShortRootFamily_of_eq (by decide) (fun t => rfl) f12
  | 2, 0, _ => exact f4ShortRootFamily_20
  | 2, 1, _ => exact f4ShortRootFamily_of_eq (by decide) (fun t => rfl) f21
  | 2, 2, h => exact absurd rfl h

end Fam

end CFSG.RankThree.PartOne.KF4
