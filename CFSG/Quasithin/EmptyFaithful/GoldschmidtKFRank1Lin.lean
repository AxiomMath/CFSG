module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Heis
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.LieType.Chevalley.RootPairCommonField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankLin3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankL4

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique

theorem outThreeBound_psl2 (K : Type) [Field K] [Finite K] :
    OutThreeBound (CFSG.GorensteinWalter.PSL2 K) := by
  have : IsCyclic (K ≃+* K) := CFSG.LieType.Chevalley.ringAut_isCyclic
  refine outThreeBound_of_pinned_cube (stdPinnedPSL2 K) stdPinnedPSL2_stable.normal
    (fun τ hτ3 hτD => ?_) (isCyclic_range_of_cyclic _) psl2_inndiag_cube
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isField_psl2_of_orderOf_prime Nat.prime_three (orderOf_eq_prime hτ3 ?_) hτD
  rintro rfl
  exact hτD (one_mem _)

theorem outThreeBound_psp4Even (F : Type) [Field F] [Finite F] [CharP F 2] :
    OutThreeBound (StatedProj (StatedSp 2 F)) := by
  have : IsCyclic (F ≃+* F) := CFSG.LieType.Chevalley.ringAut_isCyclic
  exact outThreeBound_of_pinned_cube (stdPinnedPSp4Even F) range_conjAut_normal_of_charTwo
    (fun τ hτ3 hτD => isField_psp4Even_of_pow_three_eq_one hτ3 hτD)
    (isCyclic_range_of_cyclic _) psp4Even_inndiag_cube

theorem outThreeBound_psl3 (K : Type) [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card Kˣ) :
    OutThreeBound (projectiveSL 3 K) := by
  have : IsCyclic (K ≃+* K) := CFSG.LieType.Chevalley.ringAut_isCyclic
  exact outThreeBound_of_pinned_cube (stdPinnedPSL 3 K) (stdPinnedPSL_stable (le_refl 3)).normal
    (fun τ hτ3 hτD => isField_of_pow_three_eq_one (le_refl 3) hτ3 hτD)
    (isCyclic_range_of_cyclic _) (psl_inndiag_cube (Or.inr h3))

variable {S : Type} [Group S]

theorem outThreeOrElemNine_of_statedPSL2 {K : Type} [Field K] [Finite K]
    (e : S ≃* StatedProj (StatedSL 2 K)) : OutThreeOrElemNine S :=
  Or.inl ((outThreeBound_psl2 K).of_mulEquiv
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm))

theorem outThreeOrElemNine_of_statedPSp4Even {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : S ≃* StatedProj (StatedSp 2 K)) : OutThreeOrElemNine S :=
  Or.inl ((outThreeBound_psp4Even K).of_mulEquiv e)

theorem outThreeOrElemNine_of_statedPSL3 {K : Type} [Field K] [Finite K]
    (e : S ≃* StatedProj (StatedSL 3 K)) : OutThreeOrElemNine S := by
  by_cases h3 : 3 ∣ Nat.card Kˣ
  · right
    refine Id2519.HasElemAb.of_mulEquiv e.symm
      (Lin2.OddRank.hasElemAb_nine_psl_three_of_dvd (F := K) ?_)
    rwa [Nat.card_units] at h3
  · left
    exact (outThreeBound_psl3 K h3).of_mulEquiv
      (e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)))

theorem outThreeOrElemNine_of_statedPSL4 {K : Type} [Field K]
    (e : S ≃* StatedProj (StatedSL 4 K)) : OutThreeOrElemNine S :=
  Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (Lin2.OddRank.hasElemAb_nine_psl_four K))

theorem outThreeOrElemNine_of_statedPSL5 {K : Type} [Field K]
    (e : S ≃* StatedProj (StatedSL 5 K)) : OutThreeOrElemNine S :=
  Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (Id2519.hasElemAb_nine_psl_five K))

end CFSG.Quasithin.SBd19F
