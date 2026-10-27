module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankLin3
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicNine
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggJORLNAux_notCyclic_of_card_nine {X : Type} [Group X] {A : Subgroup X}
    (hA : IsElemAbelian 3 A) (hc : Nat.card A = 9) :
    IsPGroup 3 A ∧ ¬ IsCyclic A := by
  have hpow : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hA.2 x x.2)
  refine ⟨fun x => ⟨1, by simpa using hpow x⟩, ?_⟩
  intro hcyc
  have hexp : Monoid.exponent A ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rw [IsCyclic.exponent_eq_card, hc] at hexp
  have h1 : 9 ≤ 3 := Nat.le_of_dvd (by norm_num) hexp
  omega

theorem largeEvenLabelAll_noncyclic_three_A2 {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) :
    LargeEvenLabelAll ⟨.A, 2, n⟩ fun R _ _ _ =>
      ∃ F : Subgroup R, IsPGroup 3 F ∧ ¬ IsCyclic F := by
  intro Q hQ
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hq, ?_⟩
  have hSL : LargeEvenSLGroup (Fin (2 + 1)) K = CFSG.Open.StatedSL 3 K :=
    largeEvenSLGroup_eq_statedSL 3
  have h9 : CFSG.QuasithinUnique.Id2519.HasElemAb 3 9
      (LargeEvenProj (LargeEvenSLGroup (Fin (2 + 1)) K)) := by
    rw [hSL]
    exact CFSG.QuasithinUnique.Lin2.OddRank.hasElemAb_nine_psl_three_of_dvd (F := K)
      (by rw [hK]; exact h3)
  obtain ⟨A, hA, hcard⟩ := h9
  exact ⟨A, ggJORLNAux_notCyclic_of_card_nine hA hcard⟩

theorem largeEvenLabelAll_noncyclic_three_twA {l n : ℕ}
    (hlab : LargeEvenInLambda2 ⟨.twA, l, n⟩) (hl : 3 ∣ l + 1) (h3 : 3 ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.twA, l, n⟩ fun R _ _ _ =>
      ∃ F : Subgroup R, IsPGroup 3 F ∧ ¬ IsCyclic F := by
  intro Q hQ
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hq, ?_⟩
  have hn : 1 ≤ n := hlab.1
  have hne : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : l + 1 = 3 := congrArg Prod.fst h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have hl2 : l = 2 := by omega
    have hn2 : 2 ≤ n := hlab.2.2 hl2
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn2
    omega
  have hmodel : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) .PSU (l + 1) 2 n :=
    ⟨⟨Nat.prime_two, hn, by omega, hne⟩,
      K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨A, hA, hcard⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_nine_of_psu
    (K := LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) hmodel hl h3
  exact ⟨A, ggJORLNAux_notCyclic_of_card_nine hA (by simpa using hcard)⟩

end CFSG.StandardType

end
