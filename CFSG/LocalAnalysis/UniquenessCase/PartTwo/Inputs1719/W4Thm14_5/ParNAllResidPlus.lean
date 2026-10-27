module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusLink

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidSL
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCover
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2Map

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.AGLEmbedding.LeviBlock CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem plusNodeSpace_one : plusNodeSpace K (le_refl 3) 1 = Xstar 3 K (by omega) := by
  rw [plusNodeSpace, if_neg (by decide), if_pos (by decide)]

omit [Finite K] [CharP K 2] in
private theorem plusNodeSpace_two : plusNodeSpace K (le_refl 3) 2 = flag 3 K 3 := by
  rw [plusNodeSpace, if_neg (by decide), if_neg (by decide)]

omit [Finite K] [CharP K 2] in
private theorem plusNodeStab_two_eq : plusNodeStab K (le_refl 3) {2} = plusFlagStab K 3 {3} := by
  ext g
  simp only [mem_plusNodeStab, mem_plusFlagStab, Set.mem_singleton_iff, Finset.mem_singleton,
    forall_eq, plusNodeSpace_two]

omit [CharP K 2] in
private theorem plusNodeStab_one_eq_map :
    plusNodeStab K (le_refl 3) {1} = (plusNodeStab K (le_refl 3) {2}).map
      (MulAut.conj (swapPair K (⟨3 - 1, by omega⟩ : Fin 3))).toMonoidHom := by
  set σ := swapPair K (⟨3 - 1, by omega⟩ : Fin 3)
  have hσσ : σ * σ = 1 := swapPair_mul_self _
  have hσinv : σ⁻¹ = σ := swapPair_inv _
  have hσO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) := (swapIso K _).2
  obtain ⟨hX, hXs⟩ := swapPair_smul_flag_top (K := K) (le_refl 3)
  have hconj : ∀ g ∈ orthElementaryGroup (quadPlus 3 K), σ * g * σ ∈
      orthElementaryGroup (quadPlus 3 K) := fun g hg => by
    have h := conj_mem_orthElementaryGroup hσO hg
    rwa [hσinv] at h
  ext g
  simp only [Subgroup.mem_map, mem_plusNodeStab, Set.mem_singleton_iff, forall_eq,
    plusNodeSpace_one, plusNodeSpace_two, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hσinv]
  constructor
  · rintro ⟨hgE, hg⟩
    refine ⟨σ * g * σ, ⟨hconj g hgE, ?_⟩, ?_⟩
    · rw [mul_smul, mul_smul, hX, hg, hXs]
    · simp only [← mul_assoc, hσσ, one_mul]
      rw [mul_assoc, hσσ, mul_one]
  · rintro ⟨h, ⟨hhE, hh⟩, rfl⟩
    refine ⟨hconj h hhE, ?_⟩
    rw [mul_smul, mul_smul, hXs, hh, hX]

theorem nonempty_bar2_hinf_plusNodeStab_three_two :
    Nonempty (Bar2 (Hinf (plusNodeStab K (le_refl 3) {2})) ≃*
      Matrix.SpecialLinearGroup (Fin 3) K) := by
  have := finite_plusAut (K := K) 3
  rw [plusNodeStab_two_eq]
  have hD' : ∀ d ∈ ({3} : Finset ℕ), d ≤ 3 := fun d hd => by
    rw [Finset.mem_singleton] at hd
    omega
  have hD1 : ∀ d ∈ ({3} : Finset ℕ), 1 ≤ d := fun d hd => by
    rw [Finset.mem_singleton] at hd
    omega
  have hb : 3 ∈ ({3} : Finset ℕ) := Finset.mem_singleton_self 3
  have hlen : 3 - predCut ({3} : Finset ℕ) 3 = 3 := by
    rw [show predCut ({3} : Finset ℕ) 3 = 0 by decide]
  have hker : IsPGroup 2 ↥(plusEBlockHom (K := K) hD' hb).ker := by
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb' => ?_, fun x hx => ?_⟩
    · obtain rfl : b = 3 := Finset.mem_singleton.mp hb'
      exact MonoidHom.mem_ker.mp hg
    · have ht : ({3} : Finset ℕ).sup id = 3 := by simp
      rw [ht] at hx ⊢
      rw [show 2 * 3 - 3 = 3 by norm_num] at hx
      have hgx : (g : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) x ∈ plusCutSpace 3 K 3 := by
        rw [← flag_eq_plusCutSpace le_rfl, ← smul_flag_of_mem_plusFlagStab g.2 (Or.inr hb)]
        rw [← flag_eq_plusCutSpace le_rfl] at hx
        exact ⟨x, hx, rfl⟩
      exact sub_mem hgx hx
  have hSR : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (3 - predCut ({3} : Finset ℕ) 3)) K →* _).range ≤
      (plusEBlockHom (K := K) hD' hb).range := fun x hx => by
    obtain ⟨q, hq, -, -⟩ := exists_plusFlagLevi_of_mem (le_refl 3) hD' hb hx
    exact ⟨q, hq⟩
  exact KTabD.nonempty_bar2_hinf_equiv_of_leviHom_of_equiv _ (plusEBlockHom (K := K) hD' hb) hker
    _ hSR (commutator_range_plusEBlockHom_le hD' hb)
    ((slEquivToGLRange _).symm.trans
      (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) hlen))
    (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl)
    (pCore_specialLinearGroup_eq_bot 3)

theorem nonempty_bar2_hinf_plusNodeStab_three_one :
    Nonempty (Bar2 (Hinf (plusNodeStab K (le_refl 3) {1})) ≃*
      Matrix.SpecialLinearGroup (Fin 3) K) := by
  have := finite_plusAut (K := K) 3
  obtain ⟨e₁⟩ := KTabD.nonempty_bar2_hinf_map
    (MulAut.conj (swapPair K (⟨3 - 1, by omega⟩ : Fin 3))) (plusNodeStab K (le_refl 3) {2})
  rw [← plusNodeStab_one_eq_map] at e₁
  obtain ⟨e₂⟩ := nonempty_bar2_hinf_plusNodeStab_three_two (K := K)
  exact ⟨e₁.symm.trans e₂⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
