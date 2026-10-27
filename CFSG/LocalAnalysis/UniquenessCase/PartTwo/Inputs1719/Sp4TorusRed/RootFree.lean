module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.Counting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.NumberTheory

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

theorem isTorusReducible_bot : IsTorusReducible (⊥ : Subgroup (StatedSp 2 K)) := by
  refine ⟨K ∙ Pi.single (Sum.inl 0) 1, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Submodule.span_singleton_eq_bot]
    exact Pi.single_ne_zero_iff.mpr one_ne_zero
  · intro h
    have hmem : (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) ∈ K ∙ Pi.single (Sum.inl 0) 1 := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := congrFun hc (Sum.inl 1)
    simp at h1
  · rintro d ⟨s, rfl⟩ w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [coe_torusHom, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    refine Submodule.smul_mem _ _ (Submodule.mem_span_singleton.mpr ⟨(s 0 : K), ?_⟩)
    ext k
    rcases k with k | k <;> fin_cases k <;> simp
  · intro h hh w hw
    rw [Subgroup.mem_bot] at hh
    subst hh
    simpa using hw

variable [Finite K] [CharP K 2]

theorem eq_bot_of_isRootFree {n : ℕ} (hq : Nat.card K = 2 ^ n) (hn : 3 ≤ n) (hodd : Odd n)
    {H : Subgroup (StatedSp 2 K)} (hHH : ⁅H, H⁆ = H)
    (hX : IsRootFree (H ⊔ torus 2 K)) : H = ⊥ := by
  have hK : 8 ≤ Nat.card K := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hTX : torus 2 K ≤ H ⊔ torus 2 K := le_sup_right
  have h1 := index_modEq_one hK hTX hX
  have h2 := four_mul_index_le hK hTX hX
  have h3 := index_dvd hTX
  rw [hq] at h1 h2 h3
  have hN := eq_one_of_modEq_of_le_of_dvd hn hodd h1 h2 h3
  rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hN
  exact eq_bot_of_le_normalizer_torus hK hHH (le_sup_left.trans hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
