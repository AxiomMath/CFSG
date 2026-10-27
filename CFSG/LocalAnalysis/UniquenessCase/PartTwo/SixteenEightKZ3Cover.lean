module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Stab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16k_z3_cover {g : S16kGL6}
    (hg : g ∈ Subgroup.normalizer (s16kScal : Set S16kGL6))
    (hgD : g ∉ Subgroup.normalizer (s16kDiag : Set S16kGL6)) (v : Fin 6 → ZMod 2) (hv : v ≠ 0) :
    ∃ k ∈ Subgroup.closure ((s16kDiag : Set S16kGL6) ∪ {g}), ∃ d ∈ s16kDiag, d ≠ 1 ∧
      ((k⁻¹ * d * k : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v = v := by
  let C : Matrix (Fin 6) (Fin 6) (ZMod 2) := (g : Matrix (Fin 6) (Fin 6) (ZMod 2))
  have hnot : ¬ (∀ f ∈ s16kF0, C.mulVec f ∈ s16kF0) := fun hf => hgD (s16k_z3_stab_F0 hg hf)
  rw [not_forall] at hnot
  obtain ⟨f, hf⟩ := hnot
  rw [not_imp] at hf
  obtain ⟨hfF0, hgfF0⟩ := hf
  have hfAll : f ∈ s16kAllNonzero := s16kF0_subset_allNonzero hfF0
  have hgf_ne : C.mulVec f ≠ 0 := s16kMulVec_ne_zero_of_unit (s16kAllNonzero_mem.mp hfAll)
  have hgfAll : C.mulVec f ∈ s16kAllNonzero := s16kAllNonzero_mem.mpr hgf_ne
  have hvAll : v ∈ s16kAllNonzero := s16kAllNonzero_mem.mpr hv
  have hgf_full : C.mulVec f ∈ s16kFull := by
    rw [s16kAllNonzero_eq_union] at hgfAll
    rcases Finset.mem_union.mp hgfAll with h | h
    · exact absurd h hgfF0
    · exact h
  have hv_case : v ∈ s16kF0 ∨ v ∈ s16kFull := by
    rw [s16kAllNonzero_eq_union] at hvAll
    exact Finset.mem_union.mp hvAll
  rcases hv_case with hvF0 | hvFull
  · obtain ⟨d, hd, hdne, hdv⟩ := s16kF0_mem hvF0
    obtain ⟨u, hu, hud⟩ := s16kDiagAll_exists_unit hd
    have hune : u ≠ 1 := by
      intro h1
      apply hdne
      rw [← hud, h1]
      rfl
    refine ⟨1, Subgroup.one_mem _, u, hu, hune, ?_⟩
    simp only [inv_one, one_mul, mul_one]
    rw [hud]
    exact hdv
  · obtain ⟨d1, hd1, hd1v⟩ := s16kFull_transitive _ hgf_full _ hvFull
    obtain ⟨u1, hu1, hu1d⟩ := s16kDiagAll_exists_unit hd1
    obtain ⟨d, hd, hdne, hdf⟩ := s16kF0_mem hfF0
    obtain ⟨u, hu, hud⟩ := s16kDiagAll_exists_unit hd
    have hune : u ≠ 1 := by
      intro h1
      apply hdne
      rw [← hud, h1]
      rfl
    have huf : (u : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec f = f := by
      rw [hud]
      exact hdf
    set K : S16kGL6 := u1 * g with hK
    have hKmem : K ∈ Subgroup.closure ((s16kDiag : Set S16kGL6) ∪ {g}) := by
      rw [hK]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hu1))
        (Subgroup.subset_closure (Or.inr rfl))
    have hKval : (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (u1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
      rw [hK]
      rfl
    have hKf : (K : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec f = v := by
      rw [hKval, ← Matrix.mulVec_mulVec]
      change (u1 : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (C.mulVec f) = v
      rw [hu1d]
      exact hd1v
    have hKinvK : (K : Matrix (Fin 6) (Fin 6) (ZMod 2))⁻¹ *
        (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
    have hKinv_v : (K : Matrix (Fin 6) (Fin 6) (ZMod 2))⁻¹.mulVec v = f := by
      rw [← hKf, Matrix.mulVec_mulVec, hKinvK, Matrix.one_mulVec]
    refine ⟨K⁻¹, Subgroup.inv_mem _ hKmem, u, hu, hune, ?_⟩
    have hcoe : (((K⁻¹)⁻¹ * u * K⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
          (K : Matrix (Fin 6) (Fin 6) (ZMod 2))⁻¹ := by
      rw [inv_inv]
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
    rw [hcoe]
    calc ((K : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
          (K : Matrix (Fin 6) (Fin 6) (ZMod 2))⁻¹).mulVec v
        = (K : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            ((u : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
              ((K : Matrix (Fin 6) (Fin 6) (ZMod 2))⁻¹.mulVec v)) := by
          simp only [← Matrix.mulVec_mulVec]
      _ = (K : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            ((u : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec f) := by rw [hKinv_v]
      _ = (K : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec f := by rw [huf]
      _ = v := hKf
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
