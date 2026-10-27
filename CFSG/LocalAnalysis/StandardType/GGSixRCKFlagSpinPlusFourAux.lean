module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlag
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSpinPlusFourAlg

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.LieType.Universal QuadraticMap Matrix
open CliffordAlgebra

variable {K : Type} [Field K]

@[expose] noncomputable def rckSP4_E (u w v : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K :=
  v + polar (Spin.quadPlus 2 K) v u • w - polar (Spin.quadPlus 2 K) v w • u -
    (Spin.quadPlus 2 K w * polar (Spin.quadPlus 2 K) v u) • u

@[expose] def rckSP4_vec (a b c d : K) : Fin 2 ⊕ Fin 2 → K :=
  Sum.elim ![a, b] ![c, d]

@[expose] noncomputable def rckSP4_E1 (v : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K :=
  rckSP4_E (rckSP4_vec 0 0 0 1) (rckSP4_vec 1 0 1 0) v

@[expose] noncomputable def rckSP4_E2 (v : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K :=
  rckSP4_E (rckSP4_vec 0 0 1 0) (rckSP4_vec 0 1 0 1) v

@[expose] noncomputable def rckSP4_E3 (v : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K :=
  rckSP4_E (rckSP4_vec 0 1 0 0) (rckSP4_vec 1 0 1 0) v

private lemma rckSP4_symm_zero :
    (finSumFinEquiv (m := 2) (n := 2)).symm (0 : Fin 4) = Sum.inl 0 := by decide

private lemma rckSP4_symm_one :
    (finSumFinEquiv (m := 2) (n := 2)).symm (1 : Fin 4) = Sum.inl 1 := by decide

private lemma rckSP4_symm_two :
    (finSumFinEquiv (m := 2) (n := 2)).symm (2 : Fin 4) = Sum.inr 0 := by decide

private lemma rckSP4_symm_three :
    (finSumFinEquiv (m := 2) (n := 2)).symm (3 : Fin 4) = Sum.inr 1 := by decide

private lemma rckSP4_E1_apply (h2 : (2 : K) = 0) (v : Fin 2 ⊕ Fin 2 → K) :
    rckSP4_E1 v = rckSP4_vec (v (Sum.inl 0) + v (Sum.inl 1)) (v (Sum.inl 1))
      (v (Sum.inr 0) + v (Sum.inl 1))
      (v (Sum.inl 0) + v (Sum.inl 1) + v (Sum.inr 0) + v (Sum.inr 1)) := by
  ext x
  rcases x with i | i <;> fin_cases i <;>
    simp [rckSP4_E1, rckSP4_E, rckSP4_vec, Spin.polar_quadPlus, Spin.quadPlus_apply,
      Fin.sum_univ_two]
  all_goals try rfl
  · linear_combination - (v (Sum.inl 0) + v (Sum.inl 1) + v (Sum.inr 0)) * h2

private lemma rckSP4_E2_apply (h2 : (2 : K) = 0) (v : Fin 2 ⊕ Fin 2 → K) :
    rckSP4_E2 v = rckSP4_vec (v (Sum.inl 0)) (v (Sum.inl 0) + v (Sum.inl 1))
      (v (Sum.inl 0) + v (Sum.inl 1) + v (Sum.inr 0) + v (Sum.inr 1))
      (v (Sum.inl 0) + v (Sum.inr 1)) := by
  ext x
  rcases x with i | i <;> fin_cases i <;>
    simp [rckSP4_E2, rckSP4_E, rckSP4_vec, Spin.polar_quadPlus, Spin.quadPlus_apply,
      Fin.sum_univ_two]
  all_goals try abel_nf
  · linear_combination - (v (Sum.inl 0) + v (Sum.inl 1) + v (Sum.inr 1)) * h2

private lemma rckSP4_E3_apply (h2 : (2 : K) = 0) (v : Fin 2 ⊕ Fin 2 → K) :
    rckSP4_E3 v = rckSP4_vec (v (Sum.inl 0) + v (Sum.inr 1))
      (v (Sum.inl 0) + v (Sum.inl 1) + v (Sum.inr 0) + v (Sum.inr 1))
      (v (Sum.inr 0) + v (Sum.inr 1)) (v (Sum.inr 1)) := by
  ext x
  rcases x with i | i <;> fin_cases i <;>
    simp [rckSP4_E3, rckSP4_E, rckSP4_vec, Spin.polar_quadPlus, Spin.quadPlus_apply,
      Fin.sum_univ_two]
  all_goals try rfl
  · linear_combination - (v (Sum.inl 0) + v (Sum.inr 0) + v (Sum.inr 1)) * h2

private noncomputable def rckSP4_coord (v : Fin 2 ⊕ Fin 2 → K) : Fin 4 → K :=
  fun i => v ((finSumFinEquiv (m := 2) (n := 2)).symm i)

private lemma rckSP4_coord_E1 (h2 : (2 : K) = 0) (v : Fin 2 ⊕ Fin 2 → K) :
    rckSP4_coord (rckSP4_E1 v) = rckSP4_C1 *ᵥ rckSP4_coord v := by
  ext i
  fin_cases i <;>
    simp [rckSP4_coord, rckSP4_symm_zero, rckSP4_symm_one, rckSP4_symm_two,
      rckSP4_symm_three, rckSP4_E1_apply h2, rckSP4_vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
  all_goals abel_nf

private lemma rckSP4_coord_E2 (h2 : (2 : K) = 0) (v : Fin 2 ⊕ Fin 2 → K) :
    rckSP4_coord (rckSP4_E2 v) = rckSP4_C2 *ᵥ rckSP4_coord v := by
  ext i
  fin_cases i <;>
    simp [rckSP4_coord, rckSP4_symm_zero, rckSP4_symm_one, rckSP4_symm_two,
      rckSP4_symm_three, rckSP4_E2_apply h2, rckSP4_vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
  all_goals abel_nf

private lemma rckSP4_coord_E3 (h2 : (2 : K) = 0) (v : Fin 2 ⊕ Fin 2 → K) :
    rckSP4_coord (rckSP4_E3 v) = rckSP4_C3 *ᵥ rckSP4_coord v := by
  ext i
  fin_cases i <;>
    simp [rckSP4_coord, rckSP4_symm_zero, rckSP4_symm_one, rckSP4_symm_two,
      rckSP4_symm_three, rckSP4_E3_apply h2, rckSP4_vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
  all_goals abel_nf

theorem rckSP4_matrix_eq_one (h2 : (2 : K) = 0) (T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hT : T * T = 1)
    (h1 : ∀ v, T *ᵥ rckSP4_E1 v = rckSP4_E1 (T *ᵥ v))
    (h2' : ∀ v, T *ᵥ rckSP4_E2 v = rckSP4_E2 (T *ᵥ v))
    (h3 : ∀ v, T *ᵥ rckSP4_E3 v = rckSP4_E3 (T *ᵥ v)) : T = 1 := by
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv (m := 2) (n := 2)
  let M : Matrix (Fin 4) (Fin 4) K := T.submatrix e.symm e.symm
  have hMvec : ∀ v, M *ᵥ rckSP4_coord v = rckSP4_coord (T *ᵥ v) := by
    intro v; ext i
    have h := Equiv.sum_comp e.symm (fun k : Fin 2 ⊕ Fin 2 => T (e.symm i) k * v k)
    simpa [M, rckSP4_coord, Matrix.submatrix_apply, Matrix.mulVec, dotProduct] using h
  have hsurj : ∀ w : Fin 4 → K, ∃ v, rckSP4_coord v = w := by
    intro w
    exact ⟨fun k => w (e k), by ext i; simp [rckSP4_coord, e]⟩
  have hc1 : (M * rckSP4_C1 : Matrix (Fin 4) (Fin 4) K) = rckSP4_C1 * M := by
    apply Matrix.mulVec_injective
    funext w
    obtain ⟨v, rfl⟩ := hsurj w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← rckSP4_coord_E1 h2 v,
      hMvec (rckSP4_E1 v), h1 v, hMvec v, rckSP4_coord_E1 h2 (T *ᵥ v)]
  have hc2 : (M * rckSP4_C2 : Matrix (Fin 4) (Fin 4) K) = rckSP4_C2 * M := by
    apply Matrix.mulVec_injective
    funext w
    obtain ⟨v, rfl⟩ := hsurj w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← rckSP4_coord_E2 h2 v,
      hMvec (rckSP4_E2 v), h2' v, hMvec v, rckSP4_coord_E2 h2 (T *ᵥ v)]
  have hc3 : (M * rckSP4_C3 : Matrix (Fin 4) (Fin 4) K) = rckSP4_C3 * M := by
    apply Matrix.mulVec_injective
    funext w
    obtain ⟨v, rfl⟩ := hsurj w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← rckSP4_coord_E3 h2 v,
      hMvec (rckSP4_E3 v), h3 v, hMvec v, rckSP4_coord_E3 h2 (T *ᵥ v)]
  have hMM : (M * M : Matrix (Fin 4) (Fin 4) K) = 1 := by
    change (T.submatrix e.symm e.symm * T.submatrix e.symm e.symm : Matrix (Fin 4) (Fin 4) K) = 1
    rw [← Matrix.submatrix_mul T T e.symm e.symm e.symm e.symm.bijective, hT]
    ext i j
    simp [Matrix.one_apply, e.symm.injective.eq_iff]
  have hM1 : M = 1 := rckSP4_matrix4_eq_one h2 M hMM hc1 hc2 hc3
  ext i j
  have h := Matrix.ext_iff.mpr hM1 (e i) (e j)
  have hL : M (e i) (e j) = T i j := by simp [M, Equiv.symm_apply_apply]
  rw [hL] at h
  rw [h]
  simp [Matrix.one_apply, e.injective.eq_iff]

private lemma rckSP4_exists_spin_E_aux (h2 : (2 : K) = 0)
    {u w : Fin 2 ⊕ Fin 2 → K} (hu : Spin.quadPlus 2 K u = 0)
    (huw : polar (Spin.quadPlus 2 K) u w = 0) (hw : Spin.quadPlus 2 K w = 1) :
    ∃ y : spinGroup (Spin.quadPlus 2 K), ∀ v,
      Spin.spinAction (Spin.quadPlus 2 K) y v = rckSP4_E u w v := by
  have hmem : (1 : CliffordAlgebra (Spin.quadPlus 2 K)) +
      ι (Spin.quadPlus 2 K) w * ι (Spin.quadPlus 2 K) u ∈ spinGroup (Spin.quadPlus 2 K) := by
    have h := Spin.one_add_smul_ι_mul_ι_mem_spinGroup_of_isUnit (Spin.quadPlus 2 K) hu huw
      (by rw [hw]; exact isUnit_one) 1
    rwa [one_smul] at h
  refine ⟨⟨1 + ι (Spin.quadPlus 2 K) w * ι (Spin.quadPlus 2 K) u, hmem⟩, fun v => ?_⟩
  rw [Spin.spinAction_apply_of_coe_eq (Spin.quadPlus 2 K) hu huw rfl v]
  rfl

theorem rckSP4_exists_spin_E (h2 : (2 : K) = 0) :
    (∃ y : spinGroup (Spin.quadPlus 2 K),
      ∀ v, Spin.spinAction (Spin.quadPlus 2 K) y v = rckSP4_E1 v) ∧
    (∃ y : spinGroup (Spin.quadPlus 2 K),
      ∀ v, Spin.spinAction (Spin.quadPlus 2 K) y v = rckSP4_E2 v) ∧
    (∃ y : spinGroup (Spin.quadPlus 2 K),
      ∀ v, Spin.spinAction (Spin.quadPlus 2 K) y v = rckSP4_E3 v) := by
  have hu1 : Spin.quadPlus 2 K (rckSP4_vec 0 0 0 1) = 0 := by
    simp [Spin.quadPlus_apply, Fin.sum_univ_two, rckSP4_vec]
  have huw1 : polar (Spin.quadPlus 2 K) (rckSP4_vec 0 0 0 1)
      (rckSP4_vec 1 0 1 0) = 0 := by
    simp [Spin.polar_quadPlus, Fin.sum_univ_two, rckSP4_vec]
  have hw1 : Spin.quadPlus 2 K (rckSP4_vec 1 0 1 0) = 1 := by
    simp [Spin.quadPlus_apply, Fin.sum_univ_two, rckSP4_vec]
  have hu2 : Spin.quadPlus 2 K (rckSP4_vec 0 0 1 0) = 0 := by
    simp [Spin.quadPlus_apply, Fin.sum_univ_two, rckSP4_vec]
  have huw2 : polar (Spin.quadPlus 2 K) (rckSP4_vec 0 0 1 0)
      (rckSP4_vec 0 1 0 1) = 0 := by
    simp [Spin.polar_quadPlus, Fin.sum_univ_two, rckSP4_vec]
  have hw2 : Spin.quadPlus 2 K (rckSP4_vec 0 1 0 1) = 1 := by
    simp [Spin.quadPlus_apply, Fin.sum_univ_two, rckSP4_vec]
  have hu3 : Spin.quadPlus 2 K (rckSP4_vec 0 1 0 0) = 0 := by
    simp [Spin.quadPlus_apply, Fin.sum_univ_two, rckSP4_vec]
  have huw3 : polar (Spin.quadPlus 2 K) (rckSP4_vec 0 1 0 0)
      (rckSP4_vec 1 0 1 0) = 0 := by
    simp [Spin.polar_quadPlus, Fin.sum_univ_two, rckSP4_vec]
  have hw3 : Spin.quadPlus 2 K (rckSP4_vec 1 0 1 0) = 1 := hw1
  exact ⟨rckSP4_exists_spin_E_aux h2 hu1 huw1 hw1,
    rckSP4_exists_spin_E_aux h2 hu2 huw2 hw2,
    rckSP4_exists_spin_E_aux h2 hu3 huw3 hw3⟩

theorem rckSP4_central_sq_eq_one (h2 : (2 : K) = 0) (t : spinGroup (Spin.quadPlus 2 K))
    (ht : t ∈ Subgroup.center (spinGroup (Spin.quadPlus 2 K))) (ht2 : t * t = 1) : t = 1 := by
  obtain ⟨y1, hy1⟩ := (rckSP4_exists_spin_E h2).1
  obtain ⟨y2, hy2⟩ := (rckSP4_exists_spin_E h2).2.1
  obtain ⟨y3, hy3⟩ := (rckSP4_exists_spin_E h2).2.2
  let M := Spin.spinMatrix (Spin.quadPlus 2 K)
  have hinj : Function.Injective M :=
    (MonoidHom.ker_eq_bot_iff M).1 (Spin.ker_spinMatrix_quadPlus_eq_bot (n := 2) h2)
  have hT : (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    have h := congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (map_mul M t t)
    rw [ht2, map_one] at h
    simpa using h.symm
  have hc1 : (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (M y1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (M y1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have hcent : t * y1 = y1 * t := (Subgroup.mem_center_iff.mp ht y1).symm
    have hm : M t * M y1 = M y1 * M t := by rw [← map_mul, hcent, map_mul]
    exact congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hm
  have hc2 : (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (M y2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (M y2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have hcent : t * y2 = y2 * t := (Subgroup.mem_center_iff.mp ht y2).symm
    have hm : M t * M y2 = M y2 * M t := by rw [← map_mul, hcent, map_mul]
    exact congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hm
  have hc3 : (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (M y3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (M y3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have hcent : t * y3 = y3 * t := (Subgroup.mem_center_iff.mp ht y3).symm
    have hm : M t * M y3 = M y3 * M t := by rw [← map_mul, hcent, map_mul]
    exact congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hm
  have hcomm1 : ∀ v, (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ rckSP4_E1 v =
      rckSP4_E1 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
    intro v
    have hy1v : rckSP4_E1 v = (M y1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v := by
      conv_rhs => rw [Spin.spinMatrix_mulVec]
      exact (hy1 v).symm
    have hy1v' : rckSP4_E1 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (M y1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
      conv_rhs => rw [Spin.spinMatrix_mulVec]
      exact (hy1 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)).symm
    rw [hy1v, Matrix.mulVec_mulVec, hc1, ← Matrix.mulVec_mulVec, ← hy1v']
  have hcomm2 : ∀ v, (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ rckSP4_E2 v =
      rckSP4_E2 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
    intro v
    have hy2v : rckSP4_E2 v = (M y2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v := by
      conv_rhs => rw [Spin.spinMatrix_mulVec]
      exact (hy2 v).symm
    have hy2v' : rckSP4_E2 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (M y2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
      conv_rhs => rw [Spin.spinMatrix_mulVec]
      exact (hy2 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)).symm
    rw [hy2v, Matrix.mulVec_mulVec, hc2, ← Matrix.mulVec_mulVec, ← hy2v']
  have hcomm3 : ∀ v, (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ rckSP4_E3 v =
      rckSP4_E3 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
    intro v
    have hy3v : rckSP4_E3 v = (M y3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v := by
      conv_rhs => rw [Spin.spinMatrix_mulVec]
      exact (hy3 v).symm
    have hy3v' : rckSP4_E3 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (M y3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
      conv_rhs => rw [Spin.spinMatrix_mulVec]
      exact (hy3 ((M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)).symm
    rw [hy3v, Matrix.mulVec_mulVec, hc3, ← Matrix.mulVec_mulVec, ← hy3v']
  have hmat : (M t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 :=
    rckSP4_matrix_eq_one h2 _ hT hcomm1 hcomm2 hcomm3
  have hGL : M t = 1 := Units.ext (by simpa using hmat)
  exact hinj (hGL.trans (map_one M).symm)

end CFSG.StandardType.RCKFlag
