module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpCases
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ formJ_map
  mul_transpose_formJ_mul smul_formJ_injective)
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (exists_norm_unit)

variable {r : ℕ} {K : Type} [Field K]

private lemma spForm_add_right (y z w : Fin r ⊕ Fin r → K) :
    spForm y (z + w) = spForm y z + spForm y w := by
  unfold spForm
  rw [Matrix.mulVec_add, dotProduct_add]

private lemma spForm_smul_right (c : K) (y z : Fin r ⊕ Fin r → K) :
    spForm y (c • z) = c * spForm y z := by
  unfold spForm
  rw [Matrix.mulVec_smul, dotProduct_smul]
  rfl

private lemma map_vec_sigma (σ : K ≃+* K) (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (y : Fin r ⊕ Fin r → K) :
    (fun i => σ ((M *ᵥ y) i)) = M.map σ *ᵥ (fun i => σ (y i)) := by
  funext i
  exact RingHom.map_mulVec σ.toRingHom M y i

private lemma spForm_map (σ : K ≃+* K) (y z : Fin r ⊕ Fin r → K) :
    spForm (fun i => σ (y i)) (fun i => σ (z i)) = σ (spForm y z) := by
  have h1 : (fun i => σ ((formJ r K *ᵥ z) i)) =
      formJ r K *ᵥ (fun i => σ (z i)) := by
    rw [map_vec_sigma, formJ_map]
  unfold spForm
  rw [← h1]
  exact (RingHom.map_dotProduct σ.toRingHom y (formJ r K *ᵥ z)).symm

private lemma vecMulVec_smul_left (c : K) (a b : Fin r ⊕ Fin r → K) :
    Matrix.vecMulVec (c • a) b = c • Matrix.vecMulVec a b := by
  ext i j
  simp only [Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

private lemma vecMulVec_smul_right (c : K) (a b : Fin r ⊕ Fin r → K) :
    Matrix.vecMulVec a (c • b) = c • Matrix.vecMulVec a b := by
  ext i j
  simp only [Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

private lemma spT_smul_right (c : K) (d a : Fin r ⊕ Fin r → K) :
    spT d (c • a) = c • spT d a := by
  unfold spT
  rw [vecMulVec_smul_left]

private lemma spT_smul_left (c : K) (d a : Fin r ⊕ Fin r → K) :
    spT (c • d) a = c • spT d a := by
  unfold spT
  rw [Matrix.mulVec_smul, vecMulVec_smul_right]

private lemma spN_smul_left (c : K) (a d : Fin r ⊕ Fin r → K) :
    spN (c • a) d = c • spN a d := by
  unfold spN
  rw [spT_smul_right, spT_smul_left, smul_add]

private lemma spN_smul_right (c : K) (a d : Fin r ⊕ Fin r → K) :
    spN a (c • d) = c • spN a d := by
  rw [spN_comm a (c • d), spN_smul_left, spN_comm d a]

private lemma spN_smul_smul (c c' : K) (a d : Fin r ⊕ Fin r → K) :
    spN (c • a) (c' • d) = (c * c') • spN a d := by
  rw [spN_smul_left, spN_smul_right, smul_smul]

private lemma apply_apply_eq_of_sq_eq_one {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (x : K) :
    σ (σ x) = x := by
  have h := congrArg (fun e : K ≃+* K => e x) hσ2
  simpa [pow_two] using h

private lemma exists_fixed_of_semilinear
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hσ2 : σ ^ 2 = 1)
    {k : (Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K)}
    (hk_add : ∀ y z, k (y + z) = k y + k z)
    (hk_smul : ∀ (c : K) (y : Fin r ⊕ Fin r → K), k (c • y) = σ c • k y)
    (hk_inv : ∀ y, k (k y) = y)
    {P : (Fin r ⊕ Fin r → K) → Prop}
    (hP_add : ∀ y z, P y → P z → P (y + z))
    (hP_smul : ∀ (c : K) y, P y → P (c • y))
    (hkP : ∀ y, P y → P (k y))
    {y : Fin r ⊕ Fin r → K} (hy : P y) (hy0 : y ≠ 0) :
    ∃ w, P w ∧ w ≠ 0 ∧ k w = w := by
  obtain ⟨t, ht⟩ : ∃ t : K, σ t ≠ t := by
    by_contra hcon
    push Not at hcon
    exact hσ (RingEquiv.ext fun x => by simpa using hcon x)
  have hθ0 : t - σ t ≠ 0 := by
    intro h
    exact ht (sub_eq_zero.mp h).symm
  have hσθ : σ (t - σ t) = -(t - σ t) := by
    rw [map_sub, apply_apply_eq_of_sq_eq_one hσ2, neg_sub]
  by_cases hzy : y + k y = 0
  · have hky : k y = -y := eq_neg_of_add_eq_zero_right hzy
    refine ⟨(t - σ t) • y, hP_smul _ y hy, smul_ne_zero hθ0 hy0, ?_⟩
    rw [hk_smul, hσθ, hky, neg_smul, smul_neg, neg_neg]
  · refine ⟨y + k y, hP_add y (k y) hy (hkP y hy), hzy, ?_⟩
    rw [hk_add, hk_inv, add_comm]

private lemma semilinear_add (σ : K ≃+* K) (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (y z : Fin r ⊕ Fin r → K) :
    B *ᵥ (fun i => σ ((y + z) i)) =
      B *ᵥ (fun i => σ (y i)) + B *ᵥ (fun i => σ (z i)) := by
  have h1 : (fun i => σ ((y + z) i)) =
      (fun i => σ (y i)) + (fun i => σ (z i)) := by
    funext i
    simp
  rw [h1, Matrix.mulVec_add]

private lemma semilinear_smul (σ : K ≃+* K) (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (c : K) (y : Fin r ⊕ Fin r → K) :
    B *ᵥ (fun i => σ ((c • y) i)) = σ c • (B *ᵥ (fun i => σ (y i))) := by
  have h1 : (fun i => σ ((c • y) i)) = σ c • (fun i => σ (y i)) := by
    funext i
    simp
  rw [h1, Matrix.mulVec_smul]

private lemma semilinear_involutive (σ : K ≃+* K) (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hB : B * B.map σ = 1) (hσσ : ∀ x, σ (σ x) = x) (y : Fin r ⊕ Fin r → K) :
    B *ᵥ (fun i => σ ((B *ᵥ (fun i => σ (y i))) i)) = y := by
  rw [map_vec_sigma]
  have h1 : (fun i => σ (σ (y i))) = y := funext fun i => hσσ (y i)
  rw [h1, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

private lemma spForm_semilinear (σ : K ≃+* K)
    (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) {μ' : K}
    (hB : Bᵀ * formJ r K * B = μ' • formJ r K) (y z : Fin r ⊕ Fin r → K) :
    spForm (B *ᵥ (fun i => σ (y i))) (B *ᵥ (fun i => σ (z i))) =
      μ' * σ (spForm y z) := by
  rw [spForm_mulVec hB, spForm_map]

theorem exists_spN_inv_field [Finite K] (hr : 1 ≤ r) (A : GL (Fin r ⊕ Fin r) K) {μ : K}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = μ • formJ r K)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ2 : σ ^ 2 = 1) {d : K}
    (hd : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ = d • 1) :
    ∃ v u : Fin r ⊕ Fin r → K, v ≠ 0 ∧ u ≠ 0 ∧ spForm v u = 0 ∧
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * (spN v u).map σ *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          -spN v u := by
  classical
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have : NeZero r := ⟨by omega⟩
  have hσσ : ∀ x : K, σ (σ x) = x := fun x => apply_apply_eq_of_sq_eq_one hσ2 x
  have hAinv_mul : ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA_mul_inv : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hd0 : d ≠ 0 := by
    intro hdz
    have hzero : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ = 0 := by
      have h1 : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ = 0 := by
        rw [hd, hdz, zero_smul]
      have h2 := congrArg (fun M => ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * M) h1
      rw [← Matrix.mul_assoc, hAinv_mul, Matrix.one_mul, Matrix.mul_zero] at h2
      exact h2
    have hA0 : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by
      ext i j
      have hij : σ ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j) = 0 := by
        have h := congrFun (congrFun hzero i) j
        simpa using h
      exact σ.injective (by simpa using hij)
    exact (Units.isUnit A).ne_zero hA0
  have hmap : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = σ d • 1 := by
    have h := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K => M.map σ) hd
    have hcomp : (σ : K → K) ∘ σ = id := funext fun x => hσσ x
    rw [Matrix.map_mul, Matrix.map_map, hcomp, Matrix.map_id,
      Matrix.map_smul' (σ : K → K) d (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (fun a b => map_mul σ a b),
      Matrix.map_one (σ : K → K) (map_zero σ) (map_one σ)] at h
    exact h
  have hd1 : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1 := by
    have h2 := congrArg (fun M => ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * M) hd
    rw [← Matrix.mul_assoc, hAinv_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one] at h2
    calc (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *
          (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          (d • ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *
            (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by rw [h2]
      _ = d • (((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
            (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by rw [Matrix.smul_mul]
      _ = d • 1 := by rw [hAinv_mul]
  have hσd : σ d = d := by
    have hsame : d • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        σ d • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := hd1.symm.trans hmap
    have hentry := congrFun (congrFun hsame (Sum.inl ⟨0, by omega⟩))
      (Sum.inl ⟨0, by omega⟩)
    simpa using hentry.symm
  have hdfix : σ d⁻¹ = d⁻¹ := by rw [map_inv₀, hσd]
  obtain ⟨lam, hlam⟩ := exists_norm_unit K σ hσ2 hσ
    (Units.mk0 d⁻¹ (inv_ne_zero hd0)) hdfix
  have hlam0 : (lam : K) ≠ 0 := lam.ne_zero
  set B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := (lam : K) • (A : Matrix _ _ K) with hBdef
  set μ' : K := (lam : K) * (lam : K) * μ with hμ'def
  have hB : Bᵀ * formJ r K * B = μ' • formJ r K := by
    have h1 : Bᵀ * formJ r K * B = ((lam : K) * (lam : K) * μ) • formJ r K := by
      rw [hBdef, transpose_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, hA]
      rw [smul_smul, smul_smul]
    rwa [hμ'def]
  have hBB : B * B.map σ = 1 := by
    rw [hBdef,
      Matrix.map_smul' (σ : K → K) (lam : K) (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (fun a b => map_mul σ a b),
      Matrix.smul_mul, Matrix.mul_smul, hd, smul_smul, smul_smul, hlam,
      Units.val_mk0, inv_mul_cancel₀ hd0, one_smul]
  have hA'σ : (B.map σ)ᵀ * formJ r K * (B.map σ) = σ μ' • formJ r K := by
    have h := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K => M.map σ) hB
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      Matrix.map_smul' (σ : K → K) μ' (formJ r K) (fun a b => map_mul σ a b),
      formJ_map] at h
    exact h
  have hμ' : μ' * σ μ' = 1 := by
    have h1 := mul_transpose_formJ_mul hB (B.map σ)
    rw [hBB, hA'σ] at h1
    have h2 : (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * 1 =
        (μ' * σ μ') • formJ r K := by
      simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul] using h1
    have h3 : (1 : K) • formJ r K = (μ' * σ μ') • formJ r K := by simpa using h2
    exact (smul_formJ_injective r h3).symm
  have hμ'0 : μ' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hμ'
    exact zero_ne_one hμ'
  have hσμ' : σ μ' = μ'⁻¹ := by
    calc σ μ' = 1 * σ μ' := (one_mul _).symm
      _ = (μ'⁻¹ * μ') * σ μ' := by rw [inv_mul_cancel₀ hμ'0]
      _ = μ'⁻¹ * (μ' * σ μ') := by rw [mul_assoc]
      _ = μ'⁻¹ := by rw [hμ', mul_one]
  have hσneg : σ (-μ'⁻¹) = -μ' := by
    rw [map_neg, map_inv₀, hσμ', inv_inv]
  set h : (Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K) :=
    fun y => B *ᵥ (fun i => σ (y i)) with hhdef
  have hh_add : ∀ y z, h (y + z) = h y + h z := by
    intro y z
    rw [hhdef]
    exact semilinear_add σ B y z
  have hh_smul : ∀ (c : K) (y : Fin r ⊕ Fin r → K), h (c • y) = σ c • h y := by
    intro c y
    rw [hhdef]
    exact semilinear_smul σ B c y
  have hh_inv : ∀ y, h (h y) = y := by
    intro y
    rw [hhdef]
    exact semilinear_involutive σ B hBB hσσ y
  have hspForm : ∀ y z, spForm (h y) (h z) = μ' * σ (spForm y z) := by
    intro y z
    rw [hhdef]
    exact spForm_semilinear σ B hB y z
  have hy0 : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) :
      Fin r ⊕ Fin r → K) ≠ 0 := by
    intro hzero
    have h := congrFun hzero (Sum.inl (⟨0, by omega⟩ : Fin r))
    simp at h
  obtain ⟨v, -, hv0, hv⟩ := exists_fixed_of_semilinear hσ hσ2 (k := h) hh_add hh_smul hh_inv
    (P := fun _ => True) (fun _ _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ => trivial) trivial hy0
  set k : (Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K) := fun z => -μ'⁻¹ • h z with hkdef
  have hk_add : ∀ y z, k (y + z) = k y + k z := by
    intro y z
    rw [hkdef]
    simp only [hh_add]
    rw [smul_add]
  have hk_smul : ∀ (c : K) (y : Fin r ⊕ Fin r → K), k (c • y) = σ c • k y := by
    intro c y
    rw [hkdef]
    simp only [hh_smul]
    rw [smul_smul, smul_smul, mul_comm]
  have hk_inv : ∀ y, k (k y) = y := by
    intro y
    have hcoef : (-μ'⁻¹) * σ (-μ'⁻¹) = 1 := by
      rw [hσneg, neg_mul_neg, inv_mul_cancel₀ hμ'0]
    rw [hkdef]
    calc (fun z => -μ'⁻¹ • h z) (-μ'⁻¹ • h y) = -μ'⁻¹ • h (-μ'⁻¹ • h y) := rfl
      _ = -μ'⁻¹ • (σ (-μ'⁻¹) • h (h y)) := by rw [hh_smul]
      _ = (-μ'⁻¹ * σ (-μ'⁻¹)) • h (h y) := by rw [smul_smul]
      _ = (1 : K) • y := by rw [hcoef, hh_inv]
      _ = y := one_smul K y
  have hkP : ∀ z, spForm v z = 0 → spForm v (k z) = 0 := by
    intro z hz
    have hhz : spForm v (h z) = μ' * σ (spForm v z) := by
      have h := hspForm v z
      rwa [hv] at h
    rw [hkdef, spForm_smul_right, hhz, hz, map_zero, mul_zero, mul_zero]
  have hP_add : ∀ y z, spForm v y = 0 → spForm v z = 0 → spForm v (y + z) = 0 := by
    intro y z hy hz
    rw [spForm_add_right, hy, hz, add_zero]
  have hP_smul : ∀ (c : K) y, spForm v y = 0 → spForm v (c • y) = 0 := by
    intro c y hy
    rw [spForm_smul_right, hy, mul_zero]
  obtain ⟨u, huP, hu0, hku⟩ := exists_fixed_of_semilinear hσ hσ2 (k := k) hk_add hk_smul hk_inv
    (P := fun z => spForm v z = 0) hP_add hP_smul hkP (spForm_self v) hv0
  have hhu : h u = -μ' • u := by
    have h1 : (-μ') • k u = (-μ') • u := by rw [hku]
    rw [hkdef] at h1
    rw [smul_smul] at h1
    have hcoef : (-μ') * (-μ'⁻¹) = 1 := by
      rw [neg_mul_neg, mul_inv_cancel₀ hμ'0]
    rw [hcoef, one_smul] at h1
    exact h1
  refine ⟨v, u, hv0, hu0, huP, ?_⟩
  have hAv : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      (fun i => σ (v i)) = (lam : K)⁻¹ • v := by
    have h1 : h v = (lam : K) •
        ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (fun i => σ (v i))) := by
      rw [hhdef]
      change B *ᵥ (fun i => σ (v i)) =
        (lam : K) • ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          (fun i => σ (v i)))
      rw [hBdef, Matrix.smul_mulVec]
    rw [hv] at h1
    calc (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (fun i => σ (v i)) =
          1 • ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
            (fun i => σ (v i))) := (one_smul K _).symm
      _ = ((lam : K)⁻¹ * (lam : K)) •
            ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
              (fun i => σ (v i))) := by rw [inv_mul_cancel₀ hlam0]
      _ = (lam : K)⁻¹ • ((lam : K) •
            ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
              (fun i => σ (v i)))) := by rw [smul_smul]
      _ = (lam : K)⁻¹ • v :=
        congrArg (fun z => (lam : K)⁻¹ • z) h1.symm
  have hAu : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      (fun i => σ (u i)) = (lam : K)⁻¹ • (-μ' • u) := by
    have h1 : h u = (lam : K) •
        ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (fun i => σ (u i))) := by
      rw [hhdef]
      change B *ᵥ (fun i => σ (u i)) =
        (lam : K) • ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          (fun i => σ (u i)))
      rw [hBdef, Matrix.smul_mulVec]
    rw [hhu] at h1
    calc (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (fun i => σ (u i)) =
          1 • ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
            (fun i => σ (u i))) := (one_smul K _).symm
      _ = ((lam : K)⁻¹ * (lam : K)) •
            ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
              (fun i => σ (u i))) := by rw [inv_mul_cancel₀ hlam0]
      _ = (lam : K)⁻¹ • ((lam : K) •
            ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
              (fun i => σ (u i)))) := by rw [smul_smul]
      _ = (lam : K)⁻¹ • (-μ' • u) :=
        (congrArg (fun z => (lam : K)⁻¹ • z) h1).symm
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hμ'0
    rw [hμ'def, h0]
    ring
  have hcoef : μ⁻¹ * ((lam : K)⁻¹ * ((lam : K)⁻¹ * -μ')) = -1 := by
    rw [hμ'def]
    field_simp
  calc (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * (spN v u).map σ *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          spN (fun i => σ (v i)) (fun i => σ (u i)) *
          ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
        rw [spN_map]
    _ = μ⁻¹ • spN ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (fun i => σ (v i)))
          ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (fun i => σ (u i))) :=
        conj_spN A hA _ _
    _ = μ⁻¹ • spN ((lam : K)⁻¹ • v) ((lam : K)⁻¹ • (-μ' • u)) := by rw [hAv, hAu]
    _ = μ⁻¹ • spN ((lam : K)⁻¹ • v) (((lam : K)⁻¹ * -μ') • u) := by rw [smul_smul]
    _ = μ⁻¹ • (((lam : K)⁻¹ * ((lam : K)⁻¹ * -μ')) • spN v u) := by rw [spN_smul_smul]
    _ = (μ⁻¹ * ((lam : K)⁻¹ * ((lam : K)⁻¹ * -μ'))) • spN v u := by rw [smul_smul]
    _ = -spN v u := by rw [hcoef, neg_smul, one_smul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
