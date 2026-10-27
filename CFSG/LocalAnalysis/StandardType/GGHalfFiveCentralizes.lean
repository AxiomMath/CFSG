module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem halfTorusK_five_eq : halfTorusK 5 = halfTorus 5 := by
  unfold halfTorusK halfTorus
  congr 1
  ext t
  constructor <;> rintro ⟨k, hk, rfl⟩ <;> exact ⟨k, by omega, rfl⟩

private theorem omegaBlock_five_mem (k : Fin 5) (hk : k.val % 2 = 0) :
    omegaBlock 5 k ∈ halfTorus 5 :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

private theorem zeta5_mem_halfTorus : zeta5 ∈ halfTorus 5 := by
  rw [zeta5]
  exact mul_mem (mul_mem (omegaBlock_five_mem 0 (by decide))
    (omegaBlock_five_mem 2 (by decide))) (omegaBlock_five_mem 4 (by decide))

private theorem omegaScalar_coe' :
    (omegaScalar : Matrix (Fin 3) (Fin 3) F4) = Matrix.scalar (Fin 3) f4Omega := by
  rw [omegaScalar, Units.coe_map]
  rfl

private theorem zeta5_mem_centralizer_sl3four :
    zeta5 ∈ Subgroup.centralizer (sl3four : Set (SpecialLinearGroup (Fin 6) F2)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact Subgroup.mem_centralizer_singleton_iff.mp (sl3four_le_centralizer hs)

private theorem scalar_of_commute_transvections
    {A : Matrix (Fin 3) (Fin 3) F4}
    (h : ∀ i j : Fin 3, i ≠ j → A * (1 + Matrix.single i j (1 : F4)) =
      (1 + Matrix.single i j (1 : F4)) * A) :
    ∃ a : F4, A = Matrix.scalar (Fin 3) a := by
  have hmul : ∀ i j : Fin 3, i ≠ j →
      A * Matrix.single i j (1 : F4) = Matrix.single i j (1 : F4) * A := by
    intro i j hij
    have hh := h i j hij
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at hh
    exact add_left_cancel hh
  have key : ∀ i j : Fin 3, i ≠ j → A i i = A j j ∧ (∀ k, k ≠ i → A k i = 0) := by
    intro i j hij
    have h' := hmul i j hij
    constructor
    · have hL : (A * Matrix.single i j (1 : F4)) i j = A i i := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · simp [Matrix.single_apply]
        · intro m _ hm; simp [Matrix.single_apply, hm, Ne.symm hm]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hR : (Matrix.single i j (1 : F4) * A) i j = A j j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · simp [Matrix.single_apply]
        · intro m _ hm; simp [Matrix.single_apply, hm, Ne.symm hm]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      have := congr_fun (congr_fun h' i) j
      rwa [hL, hR] at this
    · intro k hk
      have hL : (A * Matrix.single i j (1 : F4)) k j = A k i := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · simp [Matrix.single_apply]
        · intro m _ hm; simp [Matrix.single_apply, hm, Ne.symm hm]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hR : (Matrix.single i j (1 : F4) * A) k j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro m _
        have : Matrix.single i j (1 : F4) k m = 0 := by
          simp [Matrix.single_apply, hk, Ne.symm hk]
        rw [this, zero_mul]
      have := congr_fun (congr_fun h' k) j
      rwa [hL, hR] at this
  have hd : A 0 0 = A 1 1 := (key 0 1 (by decide)).1
  have hd' : A 1 1 = A 2 2 := (key 1 2 (by decide)).1
  have hz10 : A 1 0 = 0 := (key 0 1 (by decide)).2 1 (by decide)
  have hz20 : A 2 0 = 0 := (key 0 1 (by decide)).2 2 (by decide)
  have hz01 : A 0 1 = 0 := (key 1 2 (by decide)).2 0 (by decide)
  have hz21 : A 2 1 = 0 := (key 1 2 (by decide)).2 2 (by decide)
  have hz02 : A 0 2 = 0 := (key 2 0 (by decide)).2 0 (by decide)
  have hz12 : A 1 2 = 0 := (key 2 0 (by decide)).2 1 (by decide)
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, hd, hd', hz10, hz20, hz01, hz21,
      hz02, hz12]

theorem centralizes_sl3four_iff {t : SpecialLinearGroup (Fin 6) F2} (ht : t ∈ halfTorus 5) :
    (∀ s ∈ sl3four, t * s = s * t) ↔ t ∈ Subgroup.zpowers zeta5 := by
  constructor
  · intro h
    have htZ : t ∈ Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (halfTorus_comm ht zeta5_mem_halfTorus)
    have htGL : t ∈ (resGL 3).range := by
      rw [← centralizer_zeta5]; exact htZ
    obtain ⟨g, rfl⟩ := htGL
    have hAcomm : ∀ i j : Fin 3, i ≠ j →
        (g : Matrix (Fin 3) (Fin 3) F4) * (1 + Matrix.single i j (1 : F4)) =
          (1 + Matrix.single i j (1 : F4)) * (g : Matrix (Fin 3) (Fin 3) F4) := by
      intro i j hij
      have hs : resSL 3 (SpecialLinearGroup.transvection hij (1 : F4)) ∈ sl3four :=
        ⟨_, rfl⟩
      have hh := h _ hs
      apply resMat_injective 3
      have hh' := congrArg (fun z : SpecialLinearGroup (Fin 6) F2 =>
        (z : Matrix (Fin 6) (Fin 6) F2)) hh
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_resGL, coe_resSL,
        SpecialLinearGroup.transvection_coe] at hh'
      rwa [← map_mul, ← map_mul] at hh'
    obtain ⟨a, ha⟩ :=
      scalar_of_commute_transvections (A := (g : Matrix (Fin 3) (Fin 3) F4)) hAcomm
    have ha_ne : a ≠ 0 := by
      intro h0
      have hg0 : (g : Matrix (Fin 3) (Fin 3) F4) = 0 := by
        rw [ha, h0, Matrix.scalar_apply, Matrix.diagonal_zero]
      have h1 : (1 : Matrix (Fin 3) (Fin 3) F4) = 0 := by
        calc (1 : Matrix (Fin 3) (Fin 3) F4) =
              (g : Matrix (Fin 3) (Fin 3) F4) * ↑g⁻¹ := by rw [Units.mul_inv]
          _ = 0 := by rw [hg0, zero_mul]
      exact one_ne_zero h1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a = f4Omega ^ k := by
      rcases f4_cases a with h0 | h1 | hω | hω2
      · exact absurd h0 ha_ne
      · exact ⟨0, by rw [h1, pow_zero]⟩
      · exact ⟨1, by rw [hω, pow_one]⟩
      · exact ⟨2, by rw [hω2]⟩
    have hg_eq : g = omegaScalar ^ k := by
      apply Units.ext
      rw [ha, hk, Units.val_pow_eq_pow_val, omegaScalar_coe']
      exact map_pow (Matrix.scalar (Fin 3)) f4Omega k
    refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast, hg_eq, map_pow, ← zeta5_eq]
  · intro ht_z
    have hle : Subgroup.zpowers zeta5 ≤
        Subgroup.centralizer (sl3four : Set (SpecialLinearGroup (Fin 6) F2)) :=
      Subgroup.zpowers_le.mpr zeta5_mem_centralizer_sl3four
    have hmem := hle ht_z
    rw [Subgroup.mem_centralizer_iff] at hmem
    intro s hs
    exact (hmem s hs).symm

end CFSG.StandardType.GGHalf

end
