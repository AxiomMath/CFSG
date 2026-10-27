module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClSpInv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge

open Matrix CFSG.Open
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.StandardType.WitClSp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem range_sum_succ_eq_compl_coords_zero :
    Set.range (Sum.map Fin.succ Fin.succ : Fin n ⊕ Fin n → Fin (n + 1) ⊕ Fin (n + 1)) =
      (coords (0 : Fin (n + 1)))ᶜ := by
  ext x
  rcases x with j | j
  · simp only [Set.mem_range, Set.mem_compl_iff, mem_coords, Sum.inl.injEq,
      Sum.inl_ne_inr, or_false]
    constructor
    · rintro ⟨a | a, h⟩
      · intro hj
        exact Fin.succ_ne_zero a ((Sum.inl_injective h).trans hj)
      · cases h
    · intro hj
      obtain ⟨a, ha⟩ := (show j ∈ Set.range (Fin.succ : Fin n → Fin (n + 1)) from by
        rw [Fin.range_succ]
        simpa using hj)
      exact ⟨Sum.inl a, congrArg Sum.inl ha⟩
  · simp only [Set.mem_range, Set.mem_compl_iff, mem_coords, Sum.inr.injEq,
      Sum.inr_ne_inl, false_or]
    constructor
    · rintro ⟨a | a, h⟩
      · cases h
      · intro hj
        exact Fin.succ_ne_zero a ((Sum.inr_injective h).trans hj)
    · intro hj
      obtain ⟨a, ha⟩ := (show j ∈ Set.range (Fin.succ : Fin n → Fin (n + 1)) from by
        rw [Fin.range_succ]
        simpa using hj)
      exact ⟨Sum.inr a, congrArg Sum.inr ha⟩

theorem exists_fixSpace_pair_of_rank_lt (y : StatedSp (n + 1) K)
    (hrk : (mat (n + 1) K y - 1).rank < n + 1) :
    ∃ x ∈ fixSpace y, ∃ z ∈ fixSpace y, form x z = 1 := by
  have hker : LinearMap.ker (nilL y) = fixSpace y := by
    ext x
    rw [LinearMap.mem_ker, mem_fixSpace_iff_nilL]
  have hrange : Module.finrank K (LinearMap.range (nilL y)) =
      (mat (n + 1) K y - 1).rank := by
    rw [nilL, Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]
  have hdim := LinearMap.finrank_range_add_finrank_ker (nilL y)
  rw [hker, hrange, finrank_ambient] at hdim
  have hpair : ∃ x ∈ fixSpace y, ∃ z ∈ fixSpace y, form x z ≠ 0 := by
    by_contra h
    push Not at h
    have hle := finrank_fixSpace_le h
    omega
  obtain ⟨x, hx, z, hz, hxz⟩ := hpair
  exact ⟨x, hx, (form x z)⁻¹ • z, Submodule.smul_mem _ _ hz,
    by rw [form_smul_right, inv_mul_cancel₀ hxz]⟩

theorem exists_eq_conj_spEmbed_of_rank_lt (y : StatedSp (n + 1) K)
    (hrk : (mat (n + 1) K y - 1).rank < n + 1) :
    ∃ (g : StatedSp (n + 1) K) (z : StatedSp n K),
      y = g * spEmbed Fin.succ (Fin.succ_injective n) z * g⁻¹ := by
  obtain ⟨x, hx, w, hw, hxw⟩ := exists_fixSpace_pair_of_rank_lt y hrk
  obtain ⟨g, hg₁, hg₂⟩ := exists_sp_apply_eq x w hxw
  have hfix₁ : mat (n + 1) K (g⁻¹ * y * g) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inl 0) 1 := by
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg₁,
      mem_fixSpace.mp hx, ← hg₁, mulVec_inv_mulVec]
  have hfix₂ : mat (n + 1) K (g⁻¹ * y * g) *ᵥ Pi.single (Sum.inr 0) 1 =
      Pi.single (Sum.inr 0) 1 := by
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg₂,
      mem_fixSpace.mp hw, ← hg₂, mulVec_inv_mulVec]
  have hmem := mem_suppGroup_compl_of_fix hfix₁ hfix₂
  rw [← range_sum_succ_eq_compl_coords_zero, ← range_spEmbed (Fin.succ_injective n)] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨g, z, ?_⟩
  rw [hz]
  group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge
