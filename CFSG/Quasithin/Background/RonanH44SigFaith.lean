module

public import CFSG.Quasithin.Background.RonanH44SigL

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem faith_mat_rhoF (hK : Nat.card K = (2 ^ n) ^ 2) (h : SL(3, Fq n K))
    (X : HMod n K) :
    mat (rhoF hK h X) = (h : Matrix (Fin 3) (Fin 3) (Fq n K)).map (scalF n K) * mat X *
      ((h : Matrix (Fin 3) (Fin 3) (Fq n K)).map (scalF n K))ᵀ := by
  have hbar : conjM n ((h : Matrix (Fin 3) (Fin 3) (Fq n K)).map (scalF n K)) =
      (h : Matrix (Fin 3) (Fin 3) (Fq n K)).map (scalF n K) := by
    ext i j
    simp only [conjM, Matrix.map_apply, bar_scalF]
  rw [rhoF, MonoidHom.comp_apply, mat_rho, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, tw, hbar]

private theorem faith_det_map (h : SL(3, Fq n K)) :
    ((h : Matrix (Fin 3) (Fin 3) (Fq n K)).map (scalF n K)).det = 1 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]

private theorem faith_eq_one_of_map (h : SL(3, Fq n K))
    (hH : (h : Matrix (Fin 3) (Fin 3) (Fq n K)).map (scalF n K) = 1) : h = 1 := by
  have hm : (h : Matrix (Fin 3) (Fin 3) (Fq n K)) = 1 := by
    apply Matrix.map_injective (RingHom.injective (scalF n K))
    dsimp only
    rw [Matrix.map_one (scalF n K) (map_zero (scalF n K)) (map_one (scalF n K))]
    exact hH
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun hm i) j

private theorem faith_adjugate_one (M : Matrix (Fin 3) (Fin 3) K)
    (e1 : M 1 1 * M 2 2 + M 1 2 * M 2 1 = 1) (e2 : M 0 1 * M 2 2 + M 0 2 * M 2 1 = 0)
    (e3 : M 0 1 * M 1 2 + M 0 2 * M 1 1 = 0) (e4 : M 1 0 * M 2 2 + M 1 2 * M 2 0 = 0)
    (e5 : M 0 0 * M 2 2 + M 0 2 * M 2 0 = 1) (e6 : M 0 0 * M 1 2 + M 0 2 * M 1 0 = 0)
    (e7 : M 1 0 * M 2 1 + M 1 1 * M 2 0 = 0) (e8 : M 0 0 * M 2 1 + M 0 1 * M 2 0 = 0)
    (e9 : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1) : M.adjugate = 1 := by
  rw [adjugate_fin_three, Matrix.one_fin_three]
  simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]

private theorem faith_eq_one_of_alt (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (hY : ∀ p : Fq n K × Fq n K × Fq n K, M * sigAltMat p * Mᵀ = sigAltMat p) : M = 1 := by
  have e1 : M 1 1 * M 2 2 + M 1 2 * M 2 1 = 1 := by
    have h := congrFun (congrFun (hY (0, 0, 1)) 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have e2 : M 0 1 * M 2 2 + M 0 2 * M 2 1 = 0 := by
    have h := congrFun (congrFun (hY (0, 0, 1)) 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have e3 : M 0 1 * M 1 2 + M 0 2 * M 1 1 = 0 := by
    have h := congrFun (congrFun (hY (0, 0, 1)) 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have e4 : M 1 0 * M 2 2 + M 1 2 * M 2 0 = 0 := by
    have h := congrFun (congrFun (hY (0, 1, 0)) 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have e5 : M 0 0 * M 2 2 + M 0 2 * M 2 0 = 1 := by
    have h := congrFun (congrFun (hY (0, 1, 0)) 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have e6 : M 0 0 * M 1 2 + M 0 2 * M 1 0 = 0 := by
    have h := congrFun (congrFun (hY (0, 1, 0)) 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have e7 : M 1 0 * M 2 1 + M 1 1 * M 2 0 = 0 := by
    have h := congrFun (congrFun (hY (1, 0, 0)) 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have e8 : M 0 0 * M 2 1 + M 0 1 * M 2 0 = 0 := by
    have h := congrFun (congrFun (hY (1, 0, 0)) 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have e9 : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 := by
    have h := congrFun (congrFun (hY (1, 0, 0)) 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, sigAltMat] at h
    linear_combination h
  have h1 := Matrix.mul_adjugate M
  rw [faith_adjugate_one M e1 e2 e3 e4 e5 e6 e7 e8 e9, Matrix.mul_one, hdet, one_smul] at h1
  exact h1

private theorem faith_diag_sandwich (M : Matrix (Fin 3) (Fin 3) K) (j i : Fin 3) :
    (M * Matrix.single j j (1 : K) * Mᵀ) i i = M i j * M i j := by
  fin_cases j <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three] <;> ring

private theorem faith_single_diag (i j : Fin 3) :
    (Matrix.single j j (1 : K)) i i = (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.single_apply, Matrix.one_apply, hij, Ne.symm hij]

private theorem faith_one_entry (i j : Fin 3) :
    (1 : Matrix (Fin 3) (Fin 3) K) i j = 0 ∨ (1 : Matrix (Fin 3) (Fin 3) K) i j = 1 := by
  rw [Matrix.one_apply]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem faith_eq_of_mul_self (x c : K) (hc : c = 0 ∨ c = 1) (hx : x * x = c) :
    x = c := by
  rcases hc with rfl | rfl
  · exact mul_self_eq_zero.1 hx
  · have h1 : (x - 1) * (x - 1) = 0 := by
      linear_combination hx + (1 - x) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h1)

private theorem faith_mul_self_entry (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {h : SL(3, Fq n K)}
    (hfix : ∀ u ∈ fixV (Subgroup.zpowers (sig n K)),
      rhoF hK h u * u⁻¹ ∈ commV (Subgroup.zpowers (sig n K))) (j i : Fin 3) :
    (h : Matrix (Fin 3) (Fin 3) (Fq n K)).map (scalF n K) i j *
      (h : Matrix (Fin 3) (Fin 3) (Fq n K)).map (scalF n K) i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  have hS : conjM n (Matrix.single j j (1 : K)) = Matrix.single j j (1 : K) := by
    ext a b
    simp only [conjM, Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  have hherm : (conjM n (Matrix.single j j (1 : K)))ᵀ = Matrix.single j j (1 : K) := by
    rw [hS, Matrix.transpose_single]
  have hu : mkH (Matrix.single j j (1 : K)) hherm ∈ fixV (Subgroup.zpowers (sig n K)) := by
    rw [mem_fixV_sig hK]
    intro a b
    rw [mat_mkH]
    simp only [Matrix.single_apply]
    split_ifs <;> simp
  have hm := hfix _ hu
  rw [mem_commV_sig hn hK] at hm
  have hd := hm.1 i
  rw [mat_mul, mat_inv, faith_mat_rhoF, mat_mkH, Matrix.add_apply, Matrix.neg_apply,
    faith_diag_sandwich, faith_single_diag] at hd
  linear_combination hd

theorem faith_comm (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {h : SL(3, Fq n K)}
    (hfix : ∀ u ∈ commV (Subgroup.zpowers (sig n K)), rhoF hK h u = u) : h = 1 := by
  apply faith_eq_one_of_map
  apply faith_eq_one_of_alt _ (faith_det_map h)
  intro p
  have hm := congrArg mat (hfix _ (sigAltMat_mem hn hK p))
  rw [faith_mat_rhoF, mat_mkH] at hm
  exact hm

theorem faith_fix (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {h : SL(3, Fq n K)}
    (hfix : ∀ u ∈ fixV (Subgroup.zpowers (sig n K)),
      rhoF hK h u * u⁻¹ ∈ commV (Subgroup.zpowers (sig n K))) : h = 1 := by
  apply faith_eq_one_of_map
  ext i j
  exact faith_eq_of_mul_self _ _ (faith_one_entry i j) (faith_mul_self_entry hn hK hfix j i)

theorem faith_top (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {h : SL(3, Fq n K)}
    (hfix : ∀ u : HMod n K,
      rhoF hK h u * u⁻¹ ∈ fixV (Subgroup.zpowers (sig n K))) : h = 1 := by
  refine faith_comm hn hK (fun w hw => ?_)
  rw [commV_sig_eq hK, MonoidHom.mem_range] at hw
  obtain ⟨W, rfl⟩ := hw
  have hc := ((mem_range_rhoF_iff hn hK (rhoF hK h)).1 (MonoidHom.mem_range.2 ⟨h, rfl⟩)).2
  have hcomm := Subgroup.mem_centralizer_iff.1 hc (sig n K) (Set.mem_singleton _)
  have hs : ∀ x : HMod n K, sig n K (rhoF hK h x) = rhoF hK h (sig n K x) := fun x =>
    congrArg (fun φ : MulAut (HMod n K) => φ x) hcomm
  have hst : sig n K (rhoF hK h W * W⁻¹) = rhoF hK h W * W⁻¹ :=
    mem_fixV_zpowers_iff_apply.1 (hfix W)
  rw [sigPsi_apply, map_mul, map_inv, ← hs]
  generalize ht : rhoF hK h W * W⁻¹ = t at hst
  have hgW : rhoF hK h W = t * W := by
    rw [← ht, mul_assoc, inv_mul_cancel, mul_one]
  rw [hgW, map_mul, hst, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

end CFSG.Quasithin.RonanH44
