module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

@[expose] def ggKGEp_phiOp (z : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  fun i => z (ggKGEp_phi i)

theorem ggKGEp_phiOp_io (y : Fin 4 → ℤ) : ggKGEp_phiOp (ggKGEp_io y) = ggKGEp_io y := by
  funext i
  simp only [ggKGEp_phiOp, ggKGEp_io, ggKGEp_iota_phi]

theorem ggKGEp_mat_w0_mulVec
    (z : Fin Tag.E6.rank → ℤ) :
    (ggKGEl_mat (ggKGEp_w0 .E6)).mulVec z = - ggKGEp_phiOp z := by
  funext i
  simp only [ggKGEl_mat_mulVec, ggKGEp_w0_inv_E6, ggKGEp_w0_smul_E6, dotProduct, Pi.neg_apply,
    Pi.single_apply, neg_mul, Finset.sum_neg_distrib, ggKGEp_phiOp]
  rw [Finset.sum_eq_single (ggKGEp_phi i)]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ggKGEp_mat_comm_phiOp
    {v : WeylGroup Tag.E6} (hv : v * ggKGEp_w0 .E6 = ggKGEp_w0 .E6 * v)
    (z : Fin Tag.E6.rank → ℤ) :
    (ggKGEl_mat v).mulVec (ggKGEp_phiOp z) = ggKGEp_phiOp ((ggKGEl_mat v).mulVec z) := by
  have h1 : (ggKGEl_mat v).mulVec ((ggKGEl_mat (ggKGEp_w0 .E6)).mulVec z) =
      (ggKGEl_mat (v * ggKGEp_w0 .E6)).mulVec z := by
    rw [Matrix.mulVec_mulVec, ggKGEl_mat_mul]
  have h2 : (ggKGEl_mat (v * ggKGEp_w0 .E6)).mulVec z =
      (ggKGEl_mat (ggKGEp_w0 .E6 * v)).mulVec z := by rw [hv]
  have h3 : (ggKGEl_mat (ggKGEp_w0 .E6 * v)).mulVec z =
      (ggKGEl_mat (ggKGEp_w0 .E6)).mulVec ((ggKGEl_mat v).mulVec z) := by
    rw [← ggKGEl_mat_mul, Matrix.mulVec_mulVec]
  have h := h1.trans (h2.trans h3)
  rw [ggKGEp_mat_w0_mulVec, ggKGEp_mat_w0_mulVec, Matrix.mulVec_neg, neg_inj] at h
  exact h

theorem ggKGEp_io_injective : Function.Injective ggKGEp_io := by
  intro y y' h
  funext i
  have := congrFun h (ggKGEp_sec i)
  simpa [ggKGEp_io, ggKGEp_iota_sec] using this

theorem ggKGEp_io_down {z : Fin Tag.E6.rank → ℤ} (hz : ggKGEp_phiOp z = z) :
    ggKGEp_io (fun i => z (ggKGEp_sec i)) = z := by
  funext k
  simp only [ggKGEp_io]
  rcases ggKGEp_eq_or_eq_phi_sec k with h | h
  · rw [h, ggKGEp_iota_sec]
  · rw [h, ggKGEp_iota_phi, ggKGEp_iota_sec]
    exact (congrFun hz (ggKGEp_sec (ggKGEp_iota k))).symm

theorem ggKGEp_io_eq_sum_smul (y : Fin 4 → ℤ) :
    ggKGEp_io y = ∑ j, y j • ggKGEp_io (Pi.single j 1 : Fin 4 → ℤ) := by
  funext k
  simp only [ggKGEp_io, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single (ggKGEp_iota k)]
  · simp
  · intro b _ hb; simp [hb, eq_comm]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ggKGEp_mulVec_sum (M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)
    (y : Fin 4 → ℤ) :
    M.mulVec (∑ j, y j • ggKGEp_io (Pi.single j 1 : Fin 4 → ℤ)) =
      ∑ j, y j • M.mulVec (ggKGEp_io (Pi.single j 1 : Fin 4 → ℤ)) := by
  rw [← Matrix.mulVecLin_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Matrix.mulVecLin_apply]

noncomputable def ggKGEp_mat4 (v : WeylGroup Tag.E6) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => ((ggKGEl_mat v).mulVec (ggKGEp_io (Pi.single j 1))) (ggKGEp_sec i)

theorem ggKGEp_mat4_mulVec (v : WeylGroup Tag.E6) (y : Fin 4 → ℤ) :
    (ggKGEp_mat4 v).mulVec y =
      fun i => ((ggKGEl_mat v).mulVec (ggKGEp_io y)) (ggKGEp_sec i) := by
  funext i
  conv_rhs => rw [ggKGEp_io_eq_sum_smul]
  rw [ggKGEp_mulVec_sum]
  simp only [ggKGEp_mat4, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ggKGEp_mat4_io
    {v : WeylGroup Tag.E6} (hv : v * ggKGEp_w0 .E6 = ggKGEp_w0 .E6 * v) (y : Fin 4 → ℤ) :
    ggKGEp_io ((ggKGEp_mat4 v).mulVec y) = (ggKGEl_mat v).mulVec (ggKGEp_io y) := by
  rw [ggKGEp_mat4_mulVec]
  apply ggKGEp_io_down
  rw [← ggKGEp_phiOp_io y]
  exact (ggKGEp_mat_comm_phiOp hv (ggKGEp_io y)).symm

theorem ggKGEp_mat4_mul_self
    {v : WeylGroup Tag.E6} (hv : v * ggKGEp_w0 .E6 = ggKGEp_w0 .E6 * v) (hv2 : v * v = 1) :
    ggKGEp_mat4 v * ggKGEp_mat4 v = 1 := by
  have hfun : ∀ y, (ggKGEp_mat4 v).mulVec ((ggKGEp_mat4 v).mulVec y) = y := by
    intro y
    apply ggKGEp_io_injective
    rw [ggKGEp_mat4_io hv, ggKGEp_mat4_io hv]
    rw [Matrix.mulVec_mulVec, ggKGEl_mat_mul, hv2, ggKGEl_mat_one, Matrix.one_mulVec]
  ext i j
  have h := congrFun (hfun (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, ggKGEl_mulVec_single] at h
  simpa [Matrix.one_apply, Pi.single_apply] using h

@[expose] def ggKGEp_rootCoords (γ : Fin Tag.E6.rank → ℤ) : Fin 4 → ℤ :=
  ![γ 0 + γ 5, γ 1, γ 2 + γ 4, γ 3]

theorem ggKGEp_rootCoords_single_sec (i : Fin 4) :
    ggKGEp_rootCoords (Pi.single (ggKGEp_sec i) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single i 1 := by
  fin_cases i <;> (funext j; fin_cases j <;> decide +kernel)

theorem ggKGEp_dot_io (γ : Fin Tag.E6.rank → ℤ) (y : Fin 4 → ℤ) :
    γ ⬝ᵥ ggKGEp_io y = ggKGEp_rootCoords γ ⬝ᵥ y := by
  change (∑ i : Fin 6, γ i * y (ggKGEp_iota i)) = ∑ j : Fin 4, ggKGEp_rootCoords γ j * y j
  rw [Fin.sum_univ_six, Fin.sum_univ_four]
  norm_num [ggKGEp_iota, ggKGEp_rootCoords]
  simp only [mul_comm]
  ring_nf
  rfl

@[expose] noncomputable def ggKGEp_Q4 : Matrix (Fin 4) (Fin 4) ℤ :=
  ∑ γ ∈ rootFinset Tag.E6, Matrix.vecMulVec (ggKGEp_rootCoords γ) (ggKGEp_rootCoords γ)

theorem ggKGEp_Q4_apply (i j : Fin 4) :
    ggKGEp_Q4 i j =
      ∑ γ ∈ rootFinset Tag.E6, ggKGEp_rootCoords γ i * ggKGEp_rootCoords γ j := by
  rw [ggKGEp_Q4, Matrix.sum_apply]
  rfl

theorem ggKGEp_qform_Q4 (y y' : Fin 4 → ℤ) :
    y ⬝ᵥ (ggKGEp_Q4).mulVec y' =
      ∑ γ ∈ rootFinset Tag.E6,
        (ggKGEp_rootCoords γ ⬝ᵥ y) * (ggKGEp_rootCoords γ ⬝ᵥ y') := by
  rw [ggKGEp_Q4, Matrix.sum_mulVec]
  rw [show y ⬝ᵥ (∑ γ ∈ rootFinset Tag.E6,
        (Matrix.vecMulVec (ggKGEp_rootCoords γ) (ggKGEp_rootCoords γ)).mulVec y') =
      ∑ γ ∈ rootFinset Tag.E6,
        y ⬝ᵥ (Matrix.vecMulVec (ggKGEp_rootCoords γ) (ggKGEp_rootCoords γ)).mulVec y' from by
    simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Matrix.vecMulVec_mulVec]
  simp only [dotProduct, Pi.smul_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show MulOpposite.op (∑ i, ggKGEp_rootCoords γ i * y' i) • ggKGEp_rootCoords γ x =
      ggKGEp_rootCoords γ x * (∑ i, ggKGEp_rootCoords γ i * y' i) from rfl]
  ring

theorem ggKGEp_Q4_restrict (y y' : Fin 4 → ℤ) :
    y ⬝ᵥ (ggKGEp_Q4).mulVec y' =
      (ggKGEp_io y) ⬝ᵥ (ggKGEl_Q Tag.E6).mulVec (ggKGEp_io y') := by
  rw [ggKGEp_qform_Q4, ggKGEl_qform_Q, ggKGEl_qF]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [ggKGEp_dot_io, ggKGEp_dot_io]

theorem ggKGEp_Q4_symm : (ggKGEp_Q4).transpose = ggKGEp_Q4 := by
  ext i j
  rw [Matrix.transpose_apply, ggKGEp_Q4_apply, ggKGEp_Q4_apply]
  exact Finset.sum_congr rfl fun γ _ => by ring

theorem ggKGEp_single_dot {n : ℕ} (i : Fin n) (y : Fin n → ℤ) :
    (Pi.single i 1 : Fin n → ℤ) ⬝ᵥ y = y i := by
  simp only [dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem ggKGEp_Q4_form : GGLatForm ggKGEp_Q4 := by
  refine ⟨ggKGEp_Q4_symm, fun y hy => ?_⟩
  rw [ggKGEp_qform_Q4]
  rw [show (∑ γ ∈ rootFinset Tag.E6,
        (ggKGEp_rootCoords γ ⬝ᵥ y) * (ggKGEp_rootCoords γ ⬝ᵥ y)) =
      ∑ γ ∈ rootFinset Tag.E6, (ggKGEp_rootCoords γ ⬝ᵥ y) ^ 2 from
    Finset.sum_congr rfl fun γ _ => by ring]
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hy (funext fun i => h i)
  have hmem : (Pi.single (ggKGEp_sec i) 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset Tag.E6 := by
    rw [mem_rootFinset]
    exact isRoot_single Tag.E6 (ggKGEp_sec i)
  have hpos : 0 < (ggKGEp_rootCoords (Pi.single (ggKGEp_sec i) 1) ⬝ᵥ y) ^ 2 := by
    rw [ggKGEp_rootCoords_single_sec, ggKGEp_single_dot]
    positivity
  exact Finset.sum_pos' (fun γ _ => sq_nonneg _) ⟨_, hmem, hpos⟩

theorem ggKGEp_mat4_invariant
    {v : WeylGroup Tag.E6} (hv : v * ggKGEp_w0 .E6 = ggKGEp_w0 .E6 * v) :
    (ggKGEp_mat4 v).transpose * ggKGEp_Q4 * ggKGEp_mat4 v = ggKGEp_Q4 := by
  have hfun : ∀ y : Fin 4 → ℤ,
      ((ggKGEp_mat4 v).transpose * ggKGEp_Q4 * ggKGEp_mat4 v).mulVec y =
        (ggKGEp_Q4).mulVec y := by
    intro y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ggKGEl_transpose_mulVec]
    funext i
    rw [ggKGEp_Q4_restrict, ggKGEp_mat4_io hv, ggKGEp_mat4_io hv]
    rw [← ggKGEp_single_dot i (ggKGEp_Q4.mulVec y), ggKGEp_Q4_restrict (Pi.single i 1) y]
    rw [ggKGEl_qform_Q, ggKGEl_qF_dual, ← ggKGEl_qform_Q]
  ext i j
  have h := congrFun (hfun (Pi.single j 1)) i
  rwa [ggKGEl_mulVec_single, ggKGEl_mulVec_single] at h

end CFSG.StandardType

end
