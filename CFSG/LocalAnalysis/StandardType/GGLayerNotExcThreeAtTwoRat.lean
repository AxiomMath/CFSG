module

public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoPlumb
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoOrders
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoKac
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoE6D4
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDispatch
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterDispatch
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple ExcThreeAtTwo

namespace ExcThreeAtTwo

section B2


theorem kacBoundaryMark_F4_two : ∀ C : Finset (Option (Fin Tag.F4.rank)), C.card = 2 →
    kacCount .F4 ![2, 3, 4, 2] C = 8 →
      3 < kacBoundaryMark (τ := .F4) ![2, 3, 4, 2] C := by
  decide +kernel

theorem not_b2Shape_of_three_F4 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 2 ∧
       (componentRoots (rootCharHom a) i).ncard = 8) :=
  not_shape_of_kacBoundaryMark S Nat.prime_three h3 facts_F4 hTp
    (fun C h1 h2 => kacBoundaryMark_F4_two C h1 h2) i

end B2

end ExcThreeAtTwo

section Rat


theorem excThreeTwoRatNotExc_E8 : ExcThreeTwoRatNotExc .E8 := by
  intro L hL hLac p₀ S hFr hq2 a hT hap h1 i hqs
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E8 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact (not_a3Shape_of_three_E8 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩).elim
    · exact typeA_ggCQ_ne_three_two S hq2 hT hap h1 i hA hr3 hqs
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S
        Nat.prime_three h3L hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
        by_contra hlt
        have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
        exact not_d4Shape_of_three_E8 S h3L hTp i ⟨hr4, by rw [hD.2, hr4]⟩
      have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hD.2, Nat.mul_assoc]
        have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
        have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) :=
          le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
        omega
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact inner_big_ggCQ_ne S hq2 hT i (Or.inr (Or.inr (Or.inr rfl))) hinner h26
      · exact outerD_ggCQ_ne S hq2 hT hap h1 i hr5 hD.2 hinner
    · have hr8 : compRank (componentRoots (rootCharHom a) i) ≤ 8 := by
        have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
        rwa [show Tag.E8.rank = 8 from rfl] at hle
      have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hE.2]
        have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
            compRank (componentRoots (rootCharHom a) i) = 7 ∨
            compRank (componentRoots (rootCharHom a) i) = 8 := by omega
        rcases hc with h6 | h7 | h8
        · rw [h6]
          norm_num [eRootCount]
        · rw [h7]
          norm_num [eRootCount]
        · rw [h8]
          norm_num [eRootCount]
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact inner_big_ggCQ_ne S hq2 hT i (Or.inr (Or.inr (Or.inr rfl))) hinner h26
      · exact outerE_ggCQ_ne S hq2 (Or.inr (Or.inr rfl)) hT hap h1 i hE.1 hE.2 hinner

theorem excThreeTwoRatNotExc_E7 : ExcThreeTwoRatNotExc .E7 := by
  intro L hL hLac p₀ S hFr hq2 a hT hap h1 i hqs
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E7 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact (not_a3Shape_of_three_E7 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩).elim
    · exact typeA_ggCQ_ne_three_two S hq2 hT hap h1 i hA hr3 hqs
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S
        Nat.prime_three h3L hTp i
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
        by_contra hlt
        have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
        exact not_d4Shape_of_three_E7 S h3L hTp i ⟨hr4, by rw [hD.2, hr4]⟩
      have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hD.2, Nat.mul_assoc]
        have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
        have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) :=
          le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
        omega
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact inner_big_ggCQ_ne S hq2 hT i (Or.inr (Or.inr (Or.inl rfl))) hinner h26
      · exact outerD_ggCQ_ne S hq2 hT hap h1 i hr5 hD.2 hinner
    · have hr7 : compRank (componentRoots (rootCharHom a) i) ≤ 7 := by
        have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
        rwa [show Tag.E7.rank = 7 from rfl] at hle
      have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hE.2]
        have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
            compRank (componentRoots (rootCharHom a) i) = 7 := by omega
        rcases hc with h6 | h7
        · rw [h6]
          norm_num [eRootCount]
        · rw [h7]
          norm_num [eRootCount]
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact inner_big_ggCQ_ne S hq2 hT i (Or.inr (Or.inr (Or.inl rfl))) hinner h26
      · exact outerE_ggCQ_ne S hq2 (Or.inr (Or.inl rfl)) hT hap h1 i hE.1 hE.2 hinner

theorem excThreeTwoRatNotExc_E6 : ExcThreeTwoRatNotExc .E6 := by
  intro L hL hLac p₀ S hFr hq2 a hT hap h1 i hqs
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact (not_a3Shape_of_three_E6 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩).elim
    · exact typeA_ggCQ_ne_three_two S hq2 hT hap h1 i hA hr3 hqs
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S
        Nat.prime_three h3L hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    · by_cases hr4 : compRank (componentRoots (rootCharHom a) i) = 4
      · exact d4Class_ggCQ_E6_two S hFr hq2 hT hap h1 i hr4 (by rw [hD.2, hr4]) hqs
      · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
        have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hD.2, Nat.mul_assoc]
          have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
          have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) :=
            le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
          omega
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · exact inner_big_ggCQ_ne S hq2 hT i (Or.inr (Or.inl rfl)) hinner h26
        · exact outerD_ggCQ_ne S hq2 hT hap h1 i hr5 hD.2 hinner
    · exact (false_of_e6Class_E S Nat.prime_three h3L hTp h1 i hE.1 hE.2).elim

theorem excThreeTwoRatNotExc_F4 : ExcThreeTwoRatNotExc .F4 := by
  intro L hL hLac p₀ S hFr hq2 a hT hap h1 i hqs
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.F4 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact (not_a3Shape_of_three_F4 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩).elim
    · exact typeA_ggCQ_ne_three_two S hq2 hT hap h1 i hA hr3 hqs
  · rcases f4_nonA_casesP Nat.prime_three (by norm_num) S h3L hTp h1 i hA with
      hB2 | ⟨-, -, -, -, hr, hn⟩
    · exact (not_b2Shape_of_three_F4 S h3L hTp i hB2).elim
    · exact bc3Class_ggCQ_F4_two S hFr hq2 hT hap h1 i hr hn hqs

theorem ggLayerNotExcThreeAtTwoTag_F4 : GGLayerNotExcThreeAtTwoTag .F4 :=
  ggLayerNotExcThreeAtTwoTag_F4_of_rat excThreeTwoRatNotExc_F4

theorem ggLayerNotExcThreeAtTwoTag_E6 : GGLayerNotExcThreeAtTwoTag .E6 :=
  ggLayerNotExcThreeAtTwoTag_E6_of_rat excThreeTwoRatNotExc_E6

theorem ggLayerNotExcThreeAtTwoTag_E7 : GGLayerNotExcThreeAtTwoTag .E7 :=
  ggLayerNotExcThreeAtTwoTag_E7_of_rat excThreeTwoRatNotExc_E7

theorem ggLayerNotExcThreeAtTwoTag_E8 : GGLayerNotExcThreeAtTwoTag .E8 :=
  ggLayerNotExcThreeAtTwoTag_E8_of_rat excThreeTwoRatNotExc_E8

theorem ggStepTwoChoiceThreeTwoRestFive_of_twistedE6
    (h : GGStepTwoChoiceThreeTwoTag .twistedE6) : GGStepTwoChoiceThreeTwoRestFive :=
  ggStepTwoChoiceThreeTwoRestFive_of_vacuous
    ⟨ggLayerNotExcThreeAtTwoTag_F4, ggLayerNotExcThreeAtTwoTag_E6, ggLayerNotExcThreeAtTwoTag_E7,
      ggLayerNotExcThreeAtTwoTag_E8, h⟩

end Rat

end CFSG.StandardType
