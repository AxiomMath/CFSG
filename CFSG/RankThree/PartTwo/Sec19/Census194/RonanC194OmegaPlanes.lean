module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Four
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

namespace OmegaEven

open CFSG.SectionRank.ClassicalEven CFSG.SectionRank.ClassicalEven.OrthRot
  CFSG.Assembly.LowTwoRank Matrix

section Four

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {Q : (ι → K) → K}

theorem four_le_pRank_three_of_orth [Finite K] [CharP K 2] {P₀ P₁ P₂ P₃ : Plane Q}
    (h₀₁ : P₀.Orth P₁) (h₀₂ : P₀.Orth P₂) (h₀₃ : P₀.Orth P₃) (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) := by
  refine four_le_pRank_statedProj P₀.rot_mem P₁.rot_mem P₂.rot_mem P₃.rot_mem P₀.rot_pow_three
    P₁.rot_pow_three P₂.rot_pow_three P₃.rot_pow_three (Plane.rot_commute h₀₁)
    (Plane.rot_commute h₀₂) (Plane.rot_commute h₀₃) (Plane.rot_commute h₁₂)
    (Plane.rot_commute h₁₃) (Plane.rot_commute h₂₃)
    (fun hc => ?_) (fun m c hc h => ?_) (fun m k c hc h => ?_) (fun m k l c hc h => ?_)
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    exact P₀.b_ne_smul_a u (P₀.rot_a.symm.trans (hu P₀.a))
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₁.b_ne_smul_a u ?_
    rw [← P₁.rot_a, ← h, mul_mulVec, hu, mulVec_smul,
      pow_mulVec_of_fix (P₀.rot_fix h₀₁.f_a h₀₁.g_a)]
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₂.b_ne_smul_a u ?_
    rw [← P₂.rot_a, ← h]
    simp only [mul_mulVec, hu, mulVec_smul, pow_mulVec_of_fix (P₁.rot_fix h₁₂.f_a h₁₂.g_a),
      pow_mulVec_of_fix (P₀.rot_fix h₀₂.f_a h₀₂.g_a)]
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₃.b_ne_smul_a u ?_
    rw [← P₃.rot_a, ← h]
    simp only [mul_mulVec, hu, mulVec_smul, pow_mulVec_of_fix (P₂.rot_fix h₂₃.f_a h₂₃.g_a),
      pow_mulVec_of_fix (P₁.rot_fix h₁₃.f_a h₁₃.g_a),
      pow_mulVec_of_fix (P₀.rot_fix h₀₃.f_a h₀₃.g_a)]

end Four

section Frames

variable {ι : Type} [DecidableEq ι] {K : Type} [Field K]

structure PairFrame (κ : Type) (Q : (ι → K) → K) where
  X : κ → ι
  Y : κ → ι
  injX : Function.Injective X
  injY : Function.Injective Y
  X_ne_Y : ∀ i j, X i ≠ Y j
  isPolar_X : ∀ i, IsPolar Q (Pi.single (X i) 1) (LinearMap.proj (Y i)) 0
  isPolar_Y : ∀ i, IsPolar Q (Pi.single (Y i) 1) (LinearMap.proj (X i)) 0

namespace PairFrame

variable {κ : Type} {Q : (ι → K) → K} (F : PairFrame κ Q)

theorem Y_ne_X (i j : κ) : F.Y j ≠ F.X i := (F.X_ne_Y i j).symm

theorem polar_X {u : ι → K} {φ : (ι → K) →ₗ[K] K} {q : K} (hu : IsPolar Q u φ q) (j : κ) :
    φ (Pi.single (F.X j) 1) = u (F.Y j) :=
  ((F.isPolar_X j).symm hu).symm

theorem polar_Y {u : ι → K} {φ : (ι → K) →ₗ[K] K} {q : K} (hu : IsPolar Q u φ q) (j : κ) :
    φ (Pi.single (F.Y j) 1) = u (F.X j) :=
  ((F.isPolar_Y j).symm hu).symm

@[expose] def hyp (i : κ) : ι → K := Pi.single (F.X i) 1 + Pi.single (F.Y i) 1

@[expose] def hypF (i : κ) : (ι → K) →ₗ[K] K :=
  (LinearMap.proj (F.Y i) : (ι → K) →ₗ[K] K) + LinearMap.proj (F.X i)

theorem isPolar_hyp (i : κ) : IsPolar Q (F.hyp i) (F.hypF i) 1 :=
  (F.isPolar_X i).add (F.isPolar_Y i) (by simp)

@[expose] def plane (i : κ) (u : ι → K) (φ : (ι → K) →ₗ[K] K) (hu : IsPolar Q u φ 1)
    (huX : u (F.X i) = 0) (huY : u (F.Y i) = 0) : Plane Q where
  a := F.hyp i
  b := Pi.single (F.X i) 1 + u
  f := F.hypF i
  g := (LinearMap.proj (F.Y i) : (ι → K) →ₗ[K] K) + φ
  isPolar_a := F.isPolar_hyp i
  isPolar_b := (F.isPolar_X i).add hu (by rw [F.polar_X hu, huY, zero_add, add_zero])
  f_b := by simp [hypF, huX, huY, F.Y_ne_X]

theorem plane_orth {i j : κ} (hij : i ≠ j) {u u' : ι → K} {φ φ' : (ι → K) →ₗ[K] K}
    {hu : IsPolar Q u φ 1} {huX : u (F.X i) = 0} {huY : u (F.Y i) = 0}
    {hu' : IsPolar Q u' φ' 1} {huX' : u' (F.X j) = 0} {huY' : u' (F.Y j) = 0}
    (h₁ : u' (F.Y i) + u' (F.X i) = 0) (h₂ : u (F.Y j) + u (F.X j) = 0)
    (h₃ : u' (F.Y i) + u (F.Y j) + φ u' = 0) :
    (F.plane i u φ hu huX huY).Orth (F.plane j u' φ' hu' huX' huY') where
  f_a := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.Y_ne_X, hij]
  f_b := by
    simp only [plane, hypF, LinearMap.add_apply, LinearMap.proj_apply, Pi.add_apply]
    simp only [Pi.single_apply, F.injX.eq_iff, F.Y_ne_X, hij, ite_false, zero_add]
    exact h₁
  g_a := by
    simp only [plane, hyp, LinearMap.add_apply, LinearMap.proj_apply, map_add, F.polar_X hu,
      F.polar_Y hu]
    simp only [Pi.single_apply, F.injY.eq_iff, F.Y_ne_X, hij, ite_false, zero_add]
    exact h₂
  g_b := by
    simp only [plane, LinearMap.add_apply, LinearMap.proj_apply, map_add, F.polar_X hu]
    simp only [Pi.single_apply, F.Y_ne_X, ite_false, zero_add]
    linear_combination h₃

@[expose] def planeHyp (i j : κ) (hij : i ≠ j) : Plane Q :=
  F.plane i (F.hyp j) (F.hypF j) (F.isPolar_hyp j)
    (by simp [hyp, F.injX.eq_iff, F.X_ne_Y, hij.symm])
    (by simp [hyp, F.injY.eq_iff, F.Y_ne_X, hij.symm])

theorem planeHyp_orth_disjoint {i j i' j' : κ} (hij : i ≠ j) (hij' : i' ≠ j') (hii' : i ≠ i')
    (hij'' : i ≠ j') (hi'j : i' ≠ j) (hjj' : j ≠ j') :
    (F.planeHyp i j hij).Orth (F.planeHyp i' j' hij') :=
  F.plane_orth hii'
    (by simp [hyp, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hij'', hij''.symm])
    (by simp [hyp, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hi'j, hi'j.symm])
    (by simp [hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hij'', hij''.symm,
      hi'j, hi'j.symm, hjj', hjj'.symm])

theorem planeHyp_orth_swap [CharP K 2] {i j : κ} (hij : i ≠ j) :
    (F.planeHyp i j hij).Orth (F.planeHyp j i hij.symm) :=
  F.plane_orth hij
    (by simp [hyp, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, CharTwo.add_self_eq_zero])
    (by simp [hyp, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, CharTwo.add_self_eq_zero])
    (by simp [hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hij, hij.symm,
      CharTwo.add_self_eq_zero])

theorem four_le_pRank_three [Fintype ι] [Finite K] [CharP K 2] (F : PairFrame (Fin 4) Q) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) :=
  four_le_pRank_three_of_orth
    (P₀ := F.planeHyp 0 1 (by decide)) (P₁ := F.planeHyp 1 0 (by decide))
    (P₂ := F.planeHyp 2 3 (by decide)) (P₃ := F.planeHyp 3 2 (by decide))
    (F.planeHyp_orth_swap _)
    (F.planeHyp_orth_disjoint _ _ (by decide) (by decide) (by decide) (by decide))
    (F.planeHyp_orth_disjoint _ _ (by decide) (by decide) (by decide) (by decide))
    (F.planeHyp_orth_disjoint _ _ (by decide) (by decide) (by decide) (by decide))
    (F.planeHyp_orth_disjoint _ _ (by decide) (by decide) (by decide) (by decide))
    (F.planeHyp_orth_swap _)

end PairFrame

@[expose] def plusPairFrame {n : ℕ} (hn : 4 ≤ n) : PairFrame (Fin 4) (StatedQuadPlus n K) where
  X i := Sum.inl (Fin.castLE hn i)
  Y i := Sum.inr (Fin.castLE hn i)
  injX _ _ h := Fin.castLE_injective _ (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective _ (Sum.inr_injective h)
  X_ne_Y _ _ := Sum.inl_ne_inr
  isPolar_X _ := isPolar_plus_inl _
  isPolar_Y _ := isPolar_plus_inr _

@[expose] def minusPairFrame {n : ℕ} (hn : 4 ≤ n - 1) (b c : K) :
    PairFrame (Fin 4) (StatedQuadMinus n K b c) where
  X i := Sum.inl (Fin.castLE hn i)
  Y i := Sum.inr (Sum.inl (Fin.castLE hn i))
  injX _ _ h := Fin.castLE_injective _ (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective _ (Sum.inl_injective (Sum.inr_injective h))
  X_ne_Y _ _ := Sum.inl_ne_inr
  isPolar_X _ := isPolar_minus_inl b c _
  isPolar_Y _ := isPolar_minus_inr b c _

theorem four_le_pRank_three_omegaPlus [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
  (plusPairFrame hn).four_le_pRank_three

theorem four_le_pRank_three_omegaMinus [Finite K] [CharP K 2] {n : ℕ} (hn : 5 ≤ n) (b c : K) :
    4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
  (minusPairFrame (by omega) b c).four_le_pRank_three

end Frames

end OmegaEven

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
