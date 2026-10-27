module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNBA1A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13
open scoped Matrix

noncomputable def s16h_ind (n : MulAut Orth3)
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) :
    (Fin 2 → GF4) ≃+ (Fin 2 → GF4) where
  toFun w := s16h_qp (n (s16h_lift w))
  invFun w := s16h_qp (n⁻¹ (s16h_lift w))
  left_inv w := by
    have hx : s16h_lift (s16h_qp (n (s16h_lift w))) * (n (s16h_lift w))⁻¹ ∈ orth3Z :=
      s16h_lift_qp_mul_inv_mem _
    have hp := s16h_orth3_normalizer_preserves_Z (inv_mem hn)
    have hmem : n⁻¹ (s16h_lift (s16h_qp (n (s16h_lift w)))) *
        (n⁻¹ (n (s16h_lift w)))⁻¹ ∈ orth3Z := by
      simpa only [map_mul, map_inv] using hp _ hx
    have hqp := s16h_qp_eq_of_mul_inv_mem hmem
    simpa [s16h_qp_lift] using hqp
  right_inv w := by
    have hx : s16h_lift (s16h_qp (n⁻¹ (s16h_lift w))) * (n⁻¹ (s16h_lift w))⁻¹ ∈ orth3Z :=
      s16h_lift_qp_mul_inv_mem _
    have hp := s16h_orth3_normalizer_preserves_Z hn
    have hmem : n (s16h_lift (s16h_qp (n⁻¹ (s16h_lift w)))) *
        (n (n⁻¹ (s16h_lift w)))⁻¹ ∈ orth3Z := by
      simpa only [map_mul, map_inv] using hp _ hx
    have hqp := s16h_qp_eq_of_mul_inv_mem hmem
    simpa [s16h_qp_lift] using hqp
  map_add' w w' := by
    have hlift : s16h_lift (w + w') = s16h_lift w * s16h_lift w' := by
      apply Multiplicative.toAdd.injective
      simp [s16h_lift]
    show s16h_qp (n (s16h_lift (w + w'))) =
      s16h_qp (n (s16h_lift w)) + s16h_qp (n (s16h_lift w'))
    rw [hlift, map_mul, s16h_qp_add]

theorem s16h_ind_qp (n : MulAut Orth3)
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) (v : Orth3) :
    s16h_ind n hn (s16h_qp v) = s16h_qp (n v) := by
  have hp := s16h_orth3_normalizer_preserves_Z hn
  have hmem : n (s16h_lift (s16h_qp v)) * (n v)⁻¹ ∈ orth3Z := by
    simpa only [map_mul, map_inv] using hp _ (s16h_lift_qp_mul_inv_mem v)
  exact s16h_qp_eq_of_mul_inv_mem hmem

theorem s16h_ind_normalizes (n : MulAut Orth3)
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) :
    NormalizesSL2 (s16h_ind n hn) := by
  intro A
  let γA : ↥(StatedSL 2 GF4) :=
    ⟨Matrix.SpecialLinearGroup.toGL A, by
      rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
      exact ⟨A, rfl⟩⟩
  have hgram : ∀ x : Orth3,
      s16h_qp (s16h_orth3Aut γA x) =
        ((A : Matrix (Fin 2) (Fin 2) GF4)).mulVec (s16h_qp x) := by
    intro x
    simpa [γA] using s16h_qp_orth3Aut γA x
  have hγA : s16h_orth3Aut γA ∈ orth3L := by
    rw [s16h_orth3L_eq_range]
    exact ⟨γA, rfl⟩
  have hmem : n * s16h_orth3Aut γA * n⁻¹ ∈ orth3L :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp hγA
  rw [s16h_orth3L_eq_range] at hmem
  obtain ⟨δ, hδ⟩ := hmem
  refine ⟨⟨(((δ : Matrix.GeneralLinearGroup (Fin 2) GF4)) :
    Matrix (Fin 2) (Fin 2) GF4), s16h_det_mem_statedSL δ⟩, fun w => ?_⟩
  have hδ' : s16h_orth3Aut δ = n * s16h_orth3Aut γA * n⁻¹ := hδ
  have hliftZ : s16h_lift (((A : Matrix (Fin 2) (Fin 2) GF4)).mulVec w) *
      (s16h_orth3Aut γA (s16h_lift w))⁻¹ ∈ orth3Z := by
    apply s16h_mem_Z_of_qp_eq
    rw [s16h_qp_lift, hgram, s16h_qp_lift]
  have hpres := s16h_orth3_normalizer_preserves_Z hn
  have hmemZ : n (s16h_lift (((A : Matrix (Fin 2) (Fin 2) GF4)).mulVec w)) *
      (n (s16h_orth3Aut γA (s16h_lift w)))⁻¹ ∈ orth3Z := by
    simpa only [map_mul, map_inv] using hpres _ hliftZ
  have heq1 : s16h_qp (n (s16h_lift (((A : Matrix (Fin 2) (Fin 2) GF4)).mulVec w))) =
      s16h_qp (n (s16h_orth3Aut γA (s16h_lift w))) := s16h_qp_eq_of_mul_inv_mem hmemZ
  have hconj : n (s16h_orth3Aut γA (s16h_lift w)) =
      s16h_orth3Aut δ (n (s16h_lift w)) := by
    have hcomm : n * s16h_orth3Aut γA = s16h_orth3Aut δ * n := by
      rw [hδ']
      group
    calc n (s16h_orth3Aut γA (s16h_lift w))
        = (n * s16h_orth3Aut γA) (s16h_lift w) := rfl
      _ = (s16h_orth3Aut δ * n) (s16h_lift w) := by rw [hcomm]
      _ = s16h_orth3Aut δ (n (s16h_lift w)) := rfl
  show s16h_qp (n (s16h_lift (((A : Matrix (Fin 2) (Fin 2) GF4)).mulVec w))) =
    ((((δ : Matrix.GeneralLinearGroup (Fin 2) GF4)) :
      Matrix (Fin 2) (Fin 2) GF4)).mulVec (s16h_qp (n (s16h_lift w)))
  rw [heq1, hconj]
  exact s16h_qp_orth3Aut δ (n (s16h_lift w))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
