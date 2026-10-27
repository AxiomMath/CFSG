module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega6Plus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusBlocks


public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

theorem weylElt_zero_smul_flag_two (K : Type) [Field K] :
    weylElt 3 K 0 • flag 3 K 2 = flag 3 K 2 := by
  have hr2 : 2 ≤ 3 := by norm_num
  have hjr : (0 : Fin 3).val + 1 < 3 := by decide
  rw [flag_eq_coordSpan, weylElt_smul_coordSpan_eq_iff hr2]
  refine image_eq_self_of_mapsTo (weylPerm_mul_self hr2 0) ?_
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_ofPred_eq] at hk
  rw [weylPerm_inl_of_lt hr2 hjr]
  refine ⟨_, ?_, rfl⟩
  simp only [Set.mem_ofPred_eq]
  by_cases hkj : k = 0
  · subst k
    rw [Equiv.swap_apply_left]
    simp only
    omega
  by_cases hkj' : k = ⟨(0 : Fin 3).val + 1, hjr⟩
  · subst k
    rw [Equiv.swap_apply_right]
    decide
  · rw [Equiv.swap_apply_of_ne_of_ne hkj hkj']
    exact hk

theorem weylElt_one_smul_flag_two_ne (K : Type) [Field K] :
    weylElt 3 K 1 • flag 3 K 2 ≠ flag 3 K 2 := by
  have hr2 : 2 ≤ 3 := by norm_num
  have hjr : (1 : Fin 3).val + 1 < 3 := by decide
  rw [flag_eq_coordSpan, Ne, weylElt_smul_coordSpan_eq_iff hr2]
  refine image_ne_self_of_mem (c := Sum.inl 1) ⟨1, by decide, rfl⟩ ?_
  rw [weylPerm_inl_of_lt hr2 hjr, Equiv.swap_apply_left]
  rintro ⟨k, hk, he⟩
  simp only [Set.mem_ofPred_eq] at hk
  rw [Sum.inl.injEq] at he
  subst he
  simp at hk

theorem rankOneParabolic_le_plusFlagStab_alpha (K : Type) [Field K] :
    rankOneParabolic K 3 0 ≤ plusFlagStab K 3 ({2, 3} : Finset ℕ) := by
  rw [rankOneParabolic, Subgroup.closure_le]
  rintro g (hg | hg)
  · refine mem_plusFlagStab.2 ⟨borel_le hg, fun d hd => ?_⟩
    have hd' : d = 2 ∨ d = 3 := by simpa using hd
    exact (mem_borel.1 hg).2 d (by omega) (by omega)
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    refine mem_plusFlagStab.2 ⟨weylElt_mem 0, fun d hd => ?_⟩
    have hd' : d = 2 ∨ d = 3 := by simpa using hd
    rcases hd' with rfl | rfl
    · exact weylElt_zero_smul_flag_two K
    · exact MulAction.mem_stabilizer_iff.mp (weylElt_zero_mem_xStab (K := K))

theorem plusFlagStab_alpha_le_rankOneParabolic (K : Type) [Field K] :
    plusFlagStab K 3 ({2, 3} : Finset ℕ) ≤ rankOneParabolic K 3 0 := by
  have hBM : borel 3 K ≤ plusFlagStab K 3 ({2, 3} : Finset ℕ) := by
    intro g hg
    refine mem_plusFlagStab.2 ⟨borel_le hg, fun d hd => ?_⟩
    have hd' : d = 2 ∨ d = 3 := by simpa using hd
    exact (mem_borel.1 hg).2 d (by omega) (by omega)
  refine (eq_closure_of_borel_le (K := K) (r := 3) (by norm_num) inf_le_left hBM).le.trans ?_
  rw [rankOneParabolic]
  refine Subgroup.closure_mono ?_
  rintro g (hg | ⟨i, hi, rfl⟩)
  · exact Or.inl hg
  · right
    rw [Set.mem_singleton_iff]
    have hi' : weylElt 3 K i ∈ plusFlagStab K 3 ({2, 3} : Finset ℕ) := hi
    have h2 := (mem_plusFlagStab.1 hi').2 2 (by simp)
    have h3 := (mem_plusFlagStab.1 hi').2 3 (by simp)
    fin_cases i
    · rfl
    · exact absurd h2 (weylElt_one_smul_flag_two_ne K)
    · exact absurd (MulAction.mem_stabilizer_iff.mpr h3) (weylElt_two_not_mem_xStab (K := K))

theorem plusFlagStab_alpha_eq_rankOneParabolic (K : Type) [Field K] :
    plusFlagStab K 3 ({2, 3} : Finset ℕ) = rankOneParabolic K 3 0 :=
  le_antisymm (plusFlagStab_alpha_le_rankOneParabolic K) (rankOneParabolic_le_plusFlagStab_alpha K)

theorem plusFlagStab_one_subgroupOf_eq (K : Type) [Field K] :
    (plusFlagStab K 3 ({1} : Finset ℕ)).subgroupOf (splitE K) =
      (UC22.pointStab K).subgroupOf (splitE K) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_plusFlagStab, UC22.mem_pointStab]
  simp only [Finset.mem_singleton, forall_eq]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem posUnip_subgroupOf_le_plusFlagStab_one (K : Type) [Field K] :
    (posUnip 3 K).subgroupOf (splitE K) ≤
      (plusFlagStab K 3 ({1} : Finset ℕ)).subgroupOf (splitE K) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact mem_plusFlagStab.2 ⟨x.2, fun d _ => (mem_posBorel.1 (posUnip_le_posBorel hx)).2 d⟩

theorem posUnip_subgroupOf_le_plusFlagStab_alpha (K : Type) [Field K] :
    (posUnip 3 K).subgroupOf (splitE K) ≤
      (plusFlagStab K 3 ({2, 3} : Finset ℕ)).subgroupOf (splitE K) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact mem_plusFlagStab.2 ⟨x.2, fun d _ => (mem_posBorel.1 (posUnip_le_posBorel hx)).2 d⟩

theorem isParabolicTwo_plusFlagStab_alpha (K : Type) [Field K] [Finite K] [CharP K 2] :
    IsParabolicTwo ↥(splitE K) ((plusFlagStab K 3 ({2, 3} : Finset ℕ)).subgroupOf (splitE K)) := by
  rw [plusFlagStab_alpha_eq_rankOneParabolic]
  exact isParabolicTwo_rankOne

theorem not_plusFlagStab_alpha_le_one (K : Type) [Field K] :
    ¬ (plusFlagStab K 3 ({2, 3} : Finset ℕ)).subgroupOf (splitE K) ≤
      (plusFlagStab K 3 ({1} : Finset ℕ)).subgroupOf (splitE K) := by
  intro h
  have h0 : (⟨weylElt 3 K 0, weylElt_mem 0⟩ : ↥(splitE K)) ∈
      (plusFlagStab K 3 ({2, 3} : Finset ℕ)).subgroupOf (splitE K) :=
    Subgroup.mem_subgroupOf.2
      (rankOneParabolic_le_plusFlagStab_alpha K (weylElt_mem_rankOneParabolic 3 0))
  have h1 := h h0
  rw [plusFlagStab_one_subgroupOf_eq, Subgroup.mem_subgroupOf] at h1
  exact weylElt_zero_not_mem_pointStab h1

theorem plusFlagStab_alpha_le_of_parabolic {K : Type} [Field K] [Finite K] [CharP K 2]
    {P : Subgroup ↥(splitE K)} (hP : IsParabolicTwo ↥(splitE K) P)
    (hU : (posUnip 3 K).subgroupOf (splitE K) ≤ P)
    (hnot : ¬ P ≤ (plusFlagStab K 3 ({1} : Finset ℕ)).subgroupOf (splitE K)) :
    (plusFlagStab K 3 ({2, 3} : Finset ℕ)).subgroupOf (splitE K) ≤ P := by
  obtain ⟨S, hS⟩ := posUnip_isSylow (K := K) (p := 2) (r := 3) (by norm_num)
    (fun a ha => map_flag_top_ne_Xstar (K := K) (by norm_num) ha)
  have hN : Subgroup.normalizer (((posUnip 3 K).subgroupOf (splitE K) : Subgroup ↥(splitE K)) :
      Set ↥(splitE K)) ≤ P := by
    have h := hP.normalizer_le S (hS ▸ hU)
    rw [← hS]
    exact h
  rw [normalizer_posUnip (K := K) (r := 3) (by norm_num)
    (fun a ha => map_flag_top_ne_Xstar (K := K) (by norm_num) ha), flagStab_eq_borel] at hN
  rw [plusFlagStab_one_subgroupOf_eq] at hnot
  rw [plusFlagStab_alpha_eq_rankOneParabolic]
  exact rankOneParabolic_subgroupOf_le_of_borel_le_of_not_le_pointStab hN hnot

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
