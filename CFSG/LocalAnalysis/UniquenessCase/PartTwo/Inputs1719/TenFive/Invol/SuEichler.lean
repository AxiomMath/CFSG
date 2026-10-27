module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem hypForm_smul_left (h : UnitaryFieldData p f K) (c : K) (x y : HypIndex r ε → K) :
    hypForm h r ε (c • x) y = h.bar c * hypForm h r ε x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]

private theorem hypForm_neg_left (h : UnitaryFieldData p f K) (x y : HypIndex r ε → K) :
    hypForm h r ε (-x) y = -hypForm h r ε x y :=
  LinearMap.map_neg₂ (hypForm h r ε) x y

private theorem hypForm_swap (h : UnitaryFieldData p f K) (x y : HypIndex r ε → K) :
    hypForm h r ε y x = h.bar (hypForm h r ε x y) :=
  ((hypForm_isSymm h).eq x y).symm

private theorem eq_of_mulVec_eq {M M' : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hMM' : ∀ y, M *ᵥ y = M' *ᵥ y) : M = M' :=
  Matrix.ext_of_mulVec_single fun j => hMM' (Pi.single j 1)

@[expose] noncomputable def hypT (h : UnitaryFieldData p f K) (c a : HypIndex r ε → K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  vecMulVec a (vecMul (fun i => h.bar (c i)) (hypGram r ε K))

theorem hypT_mulVec (h : UnitaryFieldData p f K) (c a y : HypIndex r ε → K) :
    hypT h c a *ᵥ y = hypForm h r ε c y • a := by
  rw [hypT, vecMulVec_mulVec, op_smul_eq_smul, gramForm_apply, ← dotProduct_mulVec]

@[expose] noncomputable def hypEichler (h : UnitaryFieldData p f K) (v w : HypIndex r ε → K)
    (γ : K) : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  1 + hypT h v w - hypT h w v + γ • hypT h v v

theorem hypEichler_mulVec (h : UnitaryFieldData p f K) (v w y : HypIndex r ε → K) (γ : K) :
    hypEichler h v w γ *ᵥ y =
      y + hypForm h r ε v y • w - hypForm h r ε w y • v + (γ * hypForm h r ε v y) • v := by
  simp only [hypEichler, add_mulVec, sub_mulVec, one_mulVec, smul_mulVec, hypT_mulVec, smul_smul]

private theorem hypT_zero_right (h : UnitaryFieldData p f K) (c : HypIndex r ε → K) :
    hypT h c 0 = 0 := by
  ext i j
  simp [hypT, vecMulVec]

private theorem hypT_zero_left (h : UnitaryFieldData p f K) (a : HypIndex r ε → K) :
    hypT h 0 a = 0 := by
  ext i j
  have h0 : (fun k => h.bar ((0 : HypIndex r ε → K) k)) = 0 := by
    funext k
    simp
  simp only [hypT, vecMulVec_apply, Pi.zero_apply, Matrix.zero_apply, map_zero, zero_mul,
    vecMul, dotProduct, Finset.sum_const_zero, mul_zero]

private theorem hypEichler_zero (h : UnitaryFieldData p f K) (v : HypIndex r ε → K) :
    hypEichler h v 0 0 = 1 := by
  rw [hypEichler, hypT_zero_right, hypT_zero_left, zero_smul]
  simp

theorem hypEichler_mul (h : UnitaryFieldData p f K) {v w w' : HypIndex r ε → K} (γ γ' : K)
    (hv : hypForm h r ε v v = 0) (hvw : hypForm h r ε v w = 0) (hvw' : hypForm h r ε v w' = 0) :
    hypEichler h v w γ * hypEichler h v w' γ' =
      hypEichler h v (w + w') (γ + γ' - hypForm h r ε w w') := by
  have hwv : hypForm h r ε w v = 0 := by rw [hypForm_swap, hvw, map_zero]
  refine eq_of_mulVec_eq fun y => ?_
  rw [← Matrix.mulVec_mulVec]
  simp only [hypEichler_mulVec, map_add, map_sub, map_smulₛₗ, LinearMap.add_apply,
    smul_eq_mul, hv, hvw', hwv,
    RingHom.id_apply]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem hypEichler_mul_neg (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K} {γ : K}
    (hv : hypForm h r ε v v = 0) (hvw : hypForm h r ε v w = 0)
    (hγ : γ + h.bar γ + hypForm h r ε w w = 0) :
    hypEichler h v w γ * hypEichler h v (-w) (h.bar γ) = 1 := by
  have hvw' : hypForm h r ε v (-w) = 0 := by simp [hvw]
  rw [hypEichler_mul h (w' := -w) γ (h.bar γ) hv hvw hvw']
  have h2 : γ + h.bar γ - hypForm h r ε w (-w) = 0 := by
    rw [map_neg, sub_neg_eq_add]
    exact hγ
  rw [add_neg_cancel, h2, hypEichler_zero]

theorem hypEichler_neg_mul (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K} {γ : K}
    (hv : hypForm h r ε v v = 0) (hvw : hypForm h r ε v w = 0)
    (hγ : γ + h.bar γ + hypForm h r ε w w = 0) :
    hypEichler h v (-w) (h.bar γ) * hypEichler h v w γ = 1 := by
  have hvw' : hypForm h r ε v (-w) = 0 := by simp [hvw]
  rw [hypEichler_mul h (w := -w) (w' := w) (h.bar γ) γ hv hvw' hvw]
  have h2 : h.bar γ + γ - hypForm h r ε (-w) w = 0 := by
    rw [hypForm_neg_left, sub_neg_eq_add]
    linear_combination hγ
  rw [neg_add_cancel, h2, hypEichler_zero]

theorem isometry_hypEichler (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K} {γ : K}
    (hv : hypForm h r ε v v = 0) (hvw : hypForm h r ε v w = 0)
    (hγ : γ + h.bar γ + hypForm h r ε w w = 0) :
    ((hypEichler h v w γ).map h.bar)ᵀ * hypGram r ε K * hypEichler h v w γ = hypGram r ε K := by
  refine (gramForm_isometry_iff h (hypGram r ε K) (hypEichler h v w γ)).mp ?_
  intro x y
  have hwv : hypForm h r ε w v = 0 := by rw [hypForm_swap, hvw, map_zero]
  have hxw : hypForm h r ε x w = h.bar (hypForm h r ε w x) := hypForm_swap h w x
  have hxv : hypForm h r ε x v = h.bar (hypForm h r ε v x) := hypForm_swap h v x
  rw [hypEichler_mulVec, hypEichler_mulVec]
  simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hv, hvw, hwv, hxw, hxv, map_mul]
  linear_combination (h.bar (hypForm h r ε v x) * hypForm h r ε v y) * hγ

private theorem det_one_sub_of_isNilpotent_hyp {N : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hN : IsNilpotent N) : (1 - N).det = 1 := by
  have h1 : N.charpoly = Polynomial.X ^ Fintype.card (HypIndex r ε) :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN).eq_zero
  have h2 := Matrix.eval_charpoly N 1
  rw [h1, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h2
  exact h2.symm

private theorem det_eq_one_of_sub_one_pow_three_hyp {M : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hM : (M - 1) ^ 3 = 0) : M.det = 1 := by
  have hN : IsNilpotent (1 - M) :=
    ⟨3, by rw [show (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) - M = -(M - 1) by abel,
      neg_pow, hM, mul_zero]⟩
  rw [← det_one_sub_of_isNilpotent_hyp hN, sub_sub_cancel]

private theorem eq_zero_of_forall_mulVec_eq_zero_hyp
    {N : Matrix (HypIndex r ε) (HypIndex r ε) K} (hN : ∀ v, N *ᵥ v = 0) : N = 0 := by
  ext i j
  have h1 := congrFun (hN (Pi.single j 1)) i
  rwa [mulVec_single_one, col_apply] at h1

private theorem sub_one_pow_three_eq_zero_hyp {M : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hM : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) -
      (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) = 0) : (M - 1) ^ 3 = 0 := by
  refine eq_zero_of_forall_mulVec_eq_zero_hyp fun v => ?_
  rw [pow_three, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [sub_mulVec, one_mulVec]
  exact hM v

theorem det_hypEichler (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K} (γ : K)
    (hv : hypForm h r ε v v = 0) (hvw : hypForm h r ε v w = 0) :
    (hypEichler h v w γ).det = 1 := by
  have hwv : hypForm h r ε w v = 0 := by rw [hypForm_swap, hvw, map_zero]
  have h3 : (hypEichler h v w γ - 1) ^ 3 = 0 := by
    refine sub_one_pow_three_eq_zero_hyp fun y => ?_
    simp only [hypEichler_mulVec, map_add, map_sub, map_smul, smul_eq_mul, hv, hvw, hwv]
    simp only [mul_zero, zero_smul, sub_zero, add_zero, zero_mul, sub_self]
  exact det_eq_one_of_sub_one_pow_three_hyp h3

@[expose] noncomputable def eichlerSU (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K}
    {γ : K} (hv : hypForm h r ε v v = 0) (hvw : hypForm h r ε v w = 0)
    (hγ : γ + h.bar γ + hypForm h r ε w w = 0) : hypSU h r ε :=
  ⟨⟨hypEichler h v w γ, hypEichler h v (-w) (h.bar γ), hypEichler_mul_neg h hv hvw hγ,
    hypEichler_neg_mul h hv hvw hγ⟩,
    mem_hypSU.mpr ⟨isometry_hypEichler h hv hvw hγ, det_hypEichler h γ hv hvw⟩⟩

theorem coe_eichlerSU (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K} {γ : K}
    (hv : hypForm h r ε v v = 0) (hvw : hypForm h r ε v w = 0)
    (hγ : γ + h.bar γ + hypForm h r ε w w = 0) :
    (((eichlerSU h hv hvw hγ : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = hypEichler h v w γ :=
  rfl

theorem coe_eichlerSU_inv (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K} {γ : K}
    (hv : hypForm h r ε v v = 0) (hvw : hypForm h r ε v w = 0)
    (hγ : γ + h.bar γ + hypForm h r ε w w = 0) :
    ((((eichlerSU h hv hvw hγ)⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = hypEichler h v (-w) (h.bar γ) :=
  rfl

theorem mul_hypEichler_of_mem_hypUnitary (h : UnitaryFieldData p f K)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) (v w : HypIndex r ε → K) (γ : K) :
    (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * hypEichler h v w γ =
      hypEichler h ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v)
        ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w) γ *
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  have hiso : ∀ x y, hypForm h r ε ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x)
      ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) = hypForm h r ε x y :=
    (gramForm_isometry_iff h (hypGram r ε K) (A : Matrix (HypIndex r ε) (HypIndex r ε) K)).mpr
      (mem_hypUnitary.mp hA)
  refine eq_of_mulVec_eq fun y => ?_
  simp only [← Matrix.mulVec_mulVec, hypEichler_mulVec, mulVec_add, mulVec_sub, mulVec_smul, hiso]

private theorem bar_hypGram (h : UnitaryFieldData p f K) (a b : HypIndex r ε) :
    h.bar (hypGram r ε K a b) = hypGram r ε K a b := by
  rw [hypGram_apply]
  split_ifs <;> simp

private theorem map_bar_hypT (h : UnitaryFieldData p f K) (c a : HypIndex r ε → K) :
    (hypT h c a).map h.bar =
      hypT h (fun i => h.bar (c i)) (fun i => h.bar (a i)) := by
  ext i j
  simp only [hypT, Matrix.map_apply, vecMulVec_apply, vecMul, dotProduct, map_sum, map_mul,
    UnitaryFieldData.bar_bar, bar_hypGram]

theorem map_bar_hypEichler (h : UnitaryFieldData p f K) (v w : HypIndex r ε → K) (γ : K) :
    (hypEichler h v w γ).map h.bar =
      hypEichler h (fun i => h.bar (v i)) (fun i => h.bar (w i)) (h.bar γ) := by
  simp only [hypEichler, Matrix.map_add _ (map_add h.bar), Matrix.map_sub _ (map_sub h.bar),
    Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
    map_bar_hypT]

theorem hypEichler_smul_left (h : UnitaryFieldData p f K) (κ : K) (v w : HypIndex r ε → K)
    (γ : K) : hypEichler h (κ • v) w γ = hypEichler h v (h.bar κ • w) (h.norm κ * γ) := by
  have hN : h.norm κ = κ * h.bar κ := rfl
  refine eq_of_mulVec_eq fun y => ?_
  rw [hypEichler_mulVec, hypEichler_mulVec]
  simp only [hypForm_smul_left, UnitaryFieldData.bar_bar, hN, smul_smul]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem semilinearAutHom_hypProj_inv (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {A : GL (HypIndex r ε) K} {σ : K ≃+* K}
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε) (g : hypSU h r ε)
    (hg : A * glAut σ (g : GL (HypIndex r ε) K) = ((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) * A) :
    semilinearAutHom h hr hε ⟨_, hx⟩ (hypProj h r ε g) = (hypProj h r ε g)⁻¹ := by
  rw [semilinearAutHom_apply, ← map_inv]
  congr 1
  apply Subtype.ext
  change A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ = ((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K)
  rw [hg, mul_inv_cancel_right]

theorem semilinearAutHom_eichler_inv (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {A : GL (HypIndex r ε) K} {σ : K ≃+* K}
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε)
    {v w : HypIndex r ε → K} {γ : K} (hv : hypForm h r ε v v = 0)
    (hvw : hypForm h r ε v w = 0) (hγ : γ + h.bar γ + hypForm h r ε w w = 0)
    (hA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * (hypEichler h v w γ).map σ =
      hypEichler h v (-w) (h.bar γ) * A) :
    semilinearAutHom h hr hε ⟨_, hx⟩ (hypProj h r ε (eichlerSU h hv hvw hγ)) =
      (hypProj h r ε (eichlerSU h hv hvw hγ))⁻¹ := by
  apply semilinearAutHom_hypProj_inv
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_glAut, coe_eichlerSU, coe_eichlerSU_inv]
  exact hA

structure IsEichlerDatum (h : UnitaryFieldData p f K) (v w : HypIndex r ε → K) (γ : K) : Prop where
  ne_zero : v ≠ 0
  isotropic : hypForm h r ε v v = 0
  orthogonal : hypForm h r ε v w = 0
  trace_eq : γ + h.bar γ + hypForm h r ε w w = 0
  nontrivial : w ∉ Submodule.span K {v} ∨ (w = 0 ∧ γ ≠ 0)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
