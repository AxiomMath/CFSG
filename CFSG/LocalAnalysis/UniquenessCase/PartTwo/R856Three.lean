module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R856Normal
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Three
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.R856NonNormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R856ActionThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterGeneratorChoiceX
import CFSG.LocalAnalysis.UniquenessCase.UC22R856TwF4OuterMoved
import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56SpineChain
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56SpineChainChoiceX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r856_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G)
    (S : Setup G) (hMS : S.InMSigma) : R856 (PartTwo.Three.dataOfSetup hS S) := by
  classical
  intro L hL h3 Q hQ hΓ
  by_cases hsp : IsStronglyPEmbedded 3 S.M
  · exact Or.inl hsp
  by_cases hsl : IsSL3PiType (Bar2 L)
  · exact Or.inr hsl
  exfalso
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have h614 := UC6G.uc_theorem_6_14_three hS hUC hC (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S
  have h63 := PartTwo.Three.r6_3_dataOfSetup hS hUC hC S
  have hM3 : CFSG.Open.pRank 3 S.M ≤ 3 :=
    PartTwo.Three.pRank_le_three_dataOfSetup hS S Nat.prime_three (by norm_num) le_rfl
  obtain ⟨P, hP, hQP⟩ := exists_sylow_three_ge_of_le hL.1.le hQ
  have hc : Cex856 (PartTwo.Three.dataOfSetup hS S) L Q P := ⟨hL, h3, hQ, hΓ, hsp, hsl, hP, hQP⟩
  obtain ⟨hlist, hno, -, hfus⟩ := UC22.R856Normal.fusion_of_cex856 hSg h614 h63 hc
  obtain ⟨X, hX⟩ := exists_choiceX_of_controlsFusion _ hc hfus
  by_cases hML : S.M ≤ normalizer (L : Set G)
  · have h9t := fun hT => UC22.R856Normal.false_of_normal_nine_types h63 (fun _ => hM3) hc hML hT
    rcases (list857_iff_clauses.mp hlist).resolve_left hno with hcov | hlist3
    · exact PartTwo.Three.false_of_normal_triple_cover_dataOfSetup hS hUC hC S hX hML hcov
    · rcases hlist3 with hL3 | ⟨p, f, hG2⟩ | hU3 | ⟨p, f, hD4⟩ | ⟨f, hF4⟩ | hTits | hJ2 | hHe |
        hRu | hJ4 | hM12 | hM24
      · exact h9t (Or.inl hL3)
      · by_cases hp3 : p = 3
        · subst hp3
          exact UC22.R856NormalFour.false_of_exceptional_char_three h3 (Or.inl hG2)
        · by_cases h9 : 9 ∣ (p ^ f) ^ 2 - 1
          · by_cases hf3 : 3 ∣ f
            · by_cases hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
                  (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L
              · exact PartTwo.Three.false_of_normal_g2_inner_dataOfSetup hS hUC hC S hX hML hp3 hG2
                  hInner
              · obtain ⟨x, hx, hXgen, -, hAut3, hAutOuter⟩ :=
                  exists_outer_generator_of_choiceX hX hML hInner
                exact PartTwo.Three.false_of_moved_abelian_bar_dataOfSetup hS hUC hC S hX hML hx
                  hXgen (UC22.exists_moved_abelian_of_g2_outer hG2 hp3 h9 hf3 _ hAut3 hAutOuter)
            · exact PartTwo.Three.false_of_normal_g2_of_field_degree_dataOfSetup hS hUC hC S hX hML
                hp3 hG2 hf3
          · exact hsp (UC22.R856Normal.stronglyEmbedded_of_normal_g2_of_not_nine h63
              (fun _ => hM3) hL hML hQ hΓ hG2 hp3 h9)
      · exact h9t (Or.inr (Or.inl hU3))
      · by_cases hp3 : p = 3
        · subst hp3
          exact UC22.R856NormalFour.false_of_exceptional_char_three h3 (Or.inr hD4)
        · by_cases hLX : ⁅L, X⁆ ≤ pCoreOf 2 L
          · exact PartTwo.Three.false_of_normal_d4_f4_of_commutator_dataOfSetup hS hUC hC S hX hLX
              (Or.inl ⟨p, f, hD4⟩)
          · exact PartTwo.Three.false_of_normal_trialityD4_dataOfSetup hS hUC hC S hX hML hp3
              hD4 hLX
      · by_cases hLX : ⁅L, X⁆ ≤ pCoreOf 2 L
        · exact PartTwo.Three.false_of_normal_d4_f4_of_commutator_dataOfSetup hS hUC hC S hX hLX
            (Or.inr ⟨f, hF4⟩)
        · by_cases hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
              (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L
          · exact PartTwo.Three.false_of_normal_twistedF4_dataOfSetup hS hUC hC S hX hML hF4 hLX
              hInner
          · obtain ⟨x, hx, hXgen, -, hAut3, hAutOuter⟩ :=
              exists_outer_generator_of_choiceX hX hML hInner
            exact PartTwo.Three.false_of_moved_abelian_bar_dataOfSetup hS hUC hC S hX hML hx hXgen
              (UC22.exists_moved_abelian_of_twistedF4_outer hF4 _ hAut3 hAutOuter)
      · exact h9t (Or.inr (Or.inr (Or.inl hTits)))
      · exact h9t (Or.inr (Or.inr (Or.inr (Or.inl hJ2))))
      · exact h9t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hHe)))))
      · exact h9t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hRu))))))
      · exact h9t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hJ4)))))))
      · exact h9t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM12))))))))
      · exact h9t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hM24))))))))
  · obtain ⟨h2, hcov⟩ :=
      (r858_of_r857 hSg (UC22.R856Normal.r857_of_data hSg h614) L Q P hc).resolve_left hML
    exact PartTwo.Three.false_of_nonnormal_triple_cover_dataOfSetup hS hUC hC S hMS hX hML h2 hcov

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
