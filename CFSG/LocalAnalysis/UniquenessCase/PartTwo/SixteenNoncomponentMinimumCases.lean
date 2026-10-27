module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMinimumChoice
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMinimumCyclicThreeExclusion
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSolvableRowReduction
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCyclicThreeRechoice
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL2FourTensor
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL2EightTensor
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3TensorSigma

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_exists_concl163F_of_noncomponent_minimum
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hmin : MinChoiceSupport.Conc4_136Min D V₀ V hV L)
    (hncomp : ¬ IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV)) :
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧
      barSub V₀ V hV L' ≠ ⊥ ∧ Conc4_136 D V₀ V hV L' ∧
      Concl163F D V₀ V hV L' := by
  obtain ⟨_t, _htA, _ht2, _ht1, _htr, hc⟩ := c.conc
  have to163F_of_162_4 : ∀ {L : Subgroup G},
      Case162_4 D V₀ V hV L → Concl163F D V₀ V hV L :=
    fun {L} h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have to163F_of_162_7 : Case162_7 D V₀ V hV L → Concl163F D V₀ V hV L :=
    fun h => Or.inl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  have to163F_of_163_2 : Case163_2 D V₀ V hV L → Concl163F D V₀ V hV L :=
    fun h => Or.inr (Or.inr (Or.inl h))
  have to163F_of_163_8F : Case163_8F D V₀ V hV L → Concl163F D V₀ V hV L :=
    fun h => Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  rcases hc.2.2 with h133 | hcomp2 | hcomp3 | hcomp4
  ·
    rcases concl163F_or_cyclic_three_rank_six_s1_of_conc4_133 c h133 with hdone | ⟨hcyc, hrk, hs⟩
    · exact ⟨L, c.setting, c.ne, c.conc, hdone⟩
    ·
      have hmb : mBar D.M V₀ V hV ≤ 3 := by
        obtain ⟨tmin, -, -, -, htr, heq, -⟩ := hmin
        rw [← heq]
        exact htr
      by_cases hm2 : mBar D.M V₀ V hV ≤ 2
      · exact (false_of_card_three_rk_six_min D hmin hm2 hcyc.2 hrk).elim
      · have hm3 : mBar D.M V₀ V hV = 3 := by omega
        obtain ⟨L', hS', hne', hconc', hcase, -⟩ :=
          exists_rechoice_case162_4_case168_3_of_cyclic_three_rank_six_s1
            D c.std.hx c.std.h61 c.std.h127 c.std.h1214 c.std.h638
            c.setting c.conc hm3 hs hcyc hrk
        exact ⟨L', hS', hne', hconc', to163F_of_162_4 hcase⟩
  ·
    rcases hcomp2 with ⟨K, hK, g, hg, hne, hL, hT | hT | hT⟩
    · have hcase : Case163_8F D V₀ V hV L :=
        s168e3_case163_8F_of_l3_tensor c hK hg hne hL hT.1 hT.2
      exact ⟨L, c.setting, c.ne, c.conc, to163F_of_163_8F hcase⟩
    · have hcase : Case162_7 D V₀ V hV L :=
        s168e3_case162_7_of_tensor c hK hg hne hL hT.1 hT.2
      exact ⟨L, c.setting, c.ne, c.conc, to163F_of_162_7 hcase⟩
    · have hcase : Case163_2 D V₀ V hV L :=
        case163_2_of_l2_eight_tensor c hK hg hne hL hT.1 hT.2
      exact ⟨L, c.setting, c.ne, c.conc, to163F_of_163_2 hcase⟩
  ·
    exact absurd hcomp3.1 hncomp
  ·
    exact absurd hcomp4.2.2.1 hncomp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
