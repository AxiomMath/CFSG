module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeInvol
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsC
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.RootSystem

@[expose] noncomputable def ggKGEl_mat {τ : Tag} (v : WeylGroup τ) :
    Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  Matrix.of fun i j => (v⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j

theorem ggKGEl_mat_apply {τ : Tag} (v : WeylGroup τ) (i j : Fin τ.rank) :
    ggKGEl_mat v i j = (v⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j := rfl

theorem ggKGEl_mat_mulVec {τ : Tag} (v : WeylGroup τ) (y : Fin τ.rank → ℤ) :
    (ggKGEl_mat v).mulVec y = fun i => (v⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) ⬝ᵥ y := by
  funext i
  simp only [Matrix.mulVec, ggKGEl_mat_apply, dotProduct]

theorem ggKGEl_smul_eq_sum_smul {τ : Tag} (v : WeylGroup τ) (γ : Fin τ.rank → ℤ) :
    (v • γ : Fin τ.rank → ℤ) =
      ∑ i, γ i • (v • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  conv_lhs => rw [smul_def, pi_eq_sum_univ γ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (fun j => if i = j then (1 : ℤ) else 0) = (Pi.single i 1 : Fin τ.rank → ℤ) := by
    funext j
    rw [Pi.single_apply]
    by_cases h : i = j <;> simp [h, eq_comm]
  rw [map_zsmul, hs]
  rfl

theorem ggKGEl_dot_mat_mulVec {τ : Tag} (v : WeylGroup τ) (γ y : Fin τ.rank → ℤ) :
    γ ⬝ᵥ (ggKGEl_mat v).mulVec y = (v⁻¹ • γ) ⬝ᵥ y := by
  rw [ggKGEl_mat_mulVec]
  simp only [dotProduct]
  rw [ggKGEl_smul_eq_sum_smul]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ggKGEl_mat_mul {τ : Tag} (v w : WeylGroup τ) :
    ggKGEl_mat v * ggKGEl_mat w = ggKGEl_mat (v * w) := by
  ext i j
  simp only [Matrix.mul_apply, ggKGEl_mat, Matrix.of_apply, mul_inv_rev]
  rw [mul_smul, ggKGEl_smul_eq_sum_smul w⁻¹ (v⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]

theorem ggKGEl_mat_one {τ : Tag} : ggKGEl_mat (1 : WeylGroup τ) = 1 := by
  ext i j
  simp only [ggKGEl_mat_apply, inv_one, one_smul, Matrix.one_apply]
  by_cases h : i = j <;> simp [h, Pi.single_eq_same, Pi.single_eq_of_ne, eq_comm]

theorem ggKGEl_mat_mul_self {τ : Tag} {v : WeylGroup τ} (hv : v * v = 1) :
    ggKGEl_mat v * ggKGEl_mat v = 1 := by
  rw [ggKGEl_mat_mul, hv, ggKGEl_mat_one]

theorem ggKGEl_weylTuple_zeta {τ : Tag} {K : Type} [Field K] (ζ : Kˣ) (v : WeylGroup τ)
    (y : Fin τ.rank → ℤ) :
    weylTuple v (fun i => ζ ^ y i) = fun i => ζ ^ ((ggKGEl_mat v).mulVec y i) := by
  funext i
  simp only [weylTuple, rootChar, ggKGEl_mat_mulVec, dotProduct]
  rw [show (∏ j, (ζ ^ y j) ^ ((v⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j)) =
      ∏ j, ζ ^ (y j * ((v⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j)) from
    Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

@[expose] noncomputable def ggKGEl_qF {τ : Tag} (y y' : Fin τ.rank → ℤ) : ℤ :=
  ∑ γ ∈ rootFinset τ, (γ ⬝ᵥ y) * (γ ⬝ᵥ y')

@[expose] noncomputable def ggKGEl_Q (τ : Tag) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  ∑ γ ∈ rootFinset τ, Matrix.vecMulVec γ γ

theorem ggKGEl_Q_apply {τ : Tag} (i j : Fin τ.rank) :
    ggKGEl_Q τ i j = ∑ γ ∈ rootFinset τ, γ i * γ j := by
  rw [ggKGEl_Q, Matrix.sum_apply]
  rfl

theorem ggKGEl_Q_symm {τ : Tag} : (ggKGEl_Q τ).transpose = ggKGEl_Q τ := by
  ext i j
  rw [Matrix.transpose_apply, ggKGEl_Q_apply, ggKGEl_Q_apply]
  exact Finset.sum_congr rfl fun γ _ => by ring

theorem ggKGEl_qform_Q {τ : Tag} (y y' : Fin τ.rank → ℤ) :
    y ⬝ᵥ ((ggKGEl_Q τ).mulVec y') = ggKGEl_qF y y' := by
  rw [ggKGEl_qF, ggKGEl_Q, Matrix.sum_mulVec]
  rw [show y ⬝ᵥ (∑ γ ∈ rootFinset τ, (Matrix.vecMulVec γ γ).mulVec y') =
      ∑ γ ∈ rootFinset τ, y ⬝ᵥ ((Matrix.vecMulVec γ γ).mulVec y') from by
    simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Matrix.vecMulVec_mulVec]
  simp only [dotProduct, Pi.smul_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show MulOpposite.op (∑ i, γ i * y' i) • γ x = γ x * (∑ i, γ i * y' i) from rfl]
  ring

theorem ggKGEl_sum_roots_smul
    {τ : Tag} {M : Type*} [AddCommMonoid M] (v : WeylGroup τ)
    (φ : (Fin τ.rank → ℤ) → M) :
    ∑ γ ∈ rootFinset τ, φ (v • γ) = ∑ γ ∈ rootFinset τ, φ γ := by
  let e : (Fin τ.rank → ℤ) ≃ (Fin τ.rank → ℤ) :=
    { toFun := fun γ => v • γ
      invFun := fun γ => v⁻¹ • γ
      left_inv := fun γ => by simp
      right_inv := fun γ => by simp }
  refine Finset.sum_equiv (s := rootFinset τ) (t := rootFinset τ)
    (f := fun γ => φ (v • γ)) (g := fun γ => φ γ) e ?_ ?_
  · intro γ
    simp only [e, mem_rootFinset]
    exact (isRoot_smul_iff v).symm
  · intro γ _
    rfl

theorem ggKGEl_qF_dual
    {τ : Tag} (v : WeylGroup τ) (y y' : Fin τ.rank → ℤ) :
    ggKGEl_qF ((ggKGEl_mat v).mulVec y) ((ggKGEl_mat v).mulVec y') = ggKGEl_qF y y' := by
  simp only [ggKGEl_qF]
  rw [show (∑ γ ∈ rootFinset τ,
        (γ ⬝ᵥ (ggKGEl_mat v).mulVec y) * (γ ⬝ᵥ (ggKGEl_mat v).mulVec y')) =
      ∑ γ ∈ rootFinset τ,
        ((v⁻¹ • γ) ⬝ᵥ y) * ((v⁻¹ • γ) ⬝ᵥ y') from
    Finset.sum_congr rfl fun γ _ => by rw [ggKGEl_dot_mat_mulVec, ggKGEl_dot_mat_mulVec]]
  exact ggKGEl_sum_roots_smul v⁻¹ (fun δ => (δ ⬝ᵥ y) * (δ ⬝ᵥ y'))

theorem ggKGEl_Q_form
    {τ : Tag} : GGLatForm (ggKGEl_Q τ) := by
  refine ⟨ggKGEl_Q_symm, fun y hy => ?_⟩
  rw [ggKGEl_qform_Q, ggKGEl_qF]
  rw [show (∑ γ ∈ rootFinset τ, (γ ⬝ᵥ y) * (γ ⬝ᵥ y)) =
      ∑ γ ∈ rootFinset τ, (γ ⬝ᵥ y) ^ 2 from
    Finset.sum_congr rfl fun γ _ => by ring]
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hy (funext fun i => h i)
  have hmem : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ rootFinset τ := by
    rw [mem_rootFinset]
    exact isRoot_single τ i
  have hpos : 0 < ((Pi.single i 1 : Fin τ.rank → ℤ) ⬝ᵥ y) ^ 2 := by
    have h1 : (Pi.single i 1 : Fin τ.rank → ℤ) ⬝ᵥ y = y i := by
      simp only [dotProduct, Pi.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h1]
    positivity
  exact Finset.sum_pos' (fun γ _ => sq_nonneg _) ⟨_, hmem, hpos⟩

theorem ggKGEl_transpose_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    M.transpose.mulVec z = fun i => (M.mulVec (Pi.single i 1)) ⬝ᵥ z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem ggKGEl_mulVec_single {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    M.mulVec (Pi.single j 1) = fun i => M i j := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem ggKGEl_Q_invariant
    {τ : Tag} (v : WeylGroup τ) :
    (ggKGEl_mat v).transpose * ggKGEl_Q τ * ggKGEl_mat v = ggKGEl_Q τ := by
  have hfun : ∀ y : Fin τ.rank → ℤ,
      ((ggKGEl_mat v).transpose * ggKGEl_Q τ * ggKGEl_mat v).mulVec y =
        (ggKGEl_Q τ).mulVec y := by
    intro y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ggKGEl_transpose_mulVec]
    funext i
    rw [ggKGEl_qform_Q, ggKGEl_qF_dual, ← ggKGEl_qform_Q]
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ext i j
  have h := congrFun (hfun (Pi.single j 1)) i
  rwa [ggKGEl_mulVec_single, ggKGEl_mulVec_single] at h

end CFSG.StandardType

end
