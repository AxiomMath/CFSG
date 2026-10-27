module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Swap16Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Swap16Swap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.OmegaMinusB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

theorem k144Swap16_holds : K144Swap16 := by
  classical
  intro W _ _ hW Y L₁ L₂ X hX hcomm ha₁ ha₂ hXY hXn hgen hirr hrk
  have hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hXn
  obtain ⟨g, hgY, hg⟩ := hgen
  obtain ⟨F, hFld, hFin, β, ρ, σ, hF, hM, hO⟩ :=
    exists_sqModel_of_swap16 hW hX hcomm ha₁ ha₂ (hYN hgY) hg hirr hrk
  letI : Field F := hFld
  letI : Finite F := hFin
  have hlt : bParam L₁ Y < 2 := by
    rw [bParam_lt_iff (by norm_num : 0 < 2) L₁ Y]
    intro A hA
    have hAX : A ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) :
        Set (MulAut W)) := by
      have h1 : A ≤ Subgroup.normalizer (X : Set (MulAut W)) := hA.1.trans hYN
      simpa only [hX] using h1
    by_cases hswap : ∃ t ∈ A, L₂ = L₁.map (MulAut.conj t).toMonoidHom
    · obtain ⟨t, htA, ht⟩ := hswap
      exact (swap_false_of_mem_aSet_two hF hM hO hcomm ha₁ ha₂ hA hAX htA ht).elim
    · have hAN : A ≤ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
        intro a ha
        rcases CFSG.GroupTheory.AlternatingFive.map_conj_eq_or_eq_of_normalizes hcomm ha₁ ha₂
          (hAX ha) with h | h
        · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
        · exact (hswap ⟨a, ha, h.symm⟩).elim
      exact commutator_eq_bot_of_alternatingNatural_of_mem_aSet_two hW hO hAN hA
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
