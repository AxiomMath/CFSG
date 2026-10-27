module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.Adapters.LieModelL3U3Torus
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSL3 IsSU3)

theorem two_le_pRank_three_of_isSL3_or_isSU3 {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : IsSL3 ↥X 2 ∨ IsSU3 ↥X 3) : 2 ≤ CFSG.Open.pRank 3 X := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X]
  rcases hX with hSL | hSU
  · exact CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center ↥X) Nat.prime_three
      (by norm_num)
      (CFSG.Blueprint.LieModel.two_le_pRank_psl3_of_dvd hSL.2 (r := 3) (by norm_num) (by norm_num))
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.two_le_pRank_three_of_isSU3 hSU (by norm_num)

@[expose] def R873M3 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → 2 ≤ CFSG.Open.pRank 3 X

theorem r873M3_of_r873 {G : Type} [Group G] [Finite G] {D : Data G} (h : R873 D) : R873M3 D :=
  fun L X H hmin => two_le_pRank_three_of_isSL3_or_isSU3 (h L X H hmin).1

private theorem mem_uniqueSet_of_isSubnormal_of_mem {G : Type} [Group G] [Finite G]
    {M : Subgroup G} (hmax : rankThreeIsMaxTwoLocal M) :
    ∀ {A B : Subgroup G}, CFSG.Open.IsSubnormal A B →
      A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M →
        B ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  intro A B hsub
  induction hsub with
  | refl => exact fun hA => hA
  | @step A B C hAB hnorm _ ih =>
    intro hA
    have hNB : B ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hnorm
    have hBM : B ≤ M :=
      hNB.trans (CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hmax hA)
    exact ih (CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hA hAB hBM)

theorem r874_of_m3 {G : Type} [Group G] [Finite G] (D : Data G)
    (h63 : UC6.R6_3 D) (h871 : R871 D) (h873 : R873M3 D) : R874 D := by
  have _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro L X H hmin Q hQsyl hQXsyl
  have h873h : 2 ≤ CFSG.Open.pRank 3 X := h873 L X H hmin
  have hΓP : CFSG.Open.rankThreeGamma 1 3 (Q ⊓ X) ≤ D.M := by
    rcases h871 L X H hmin (Q ⊓ X) hQXsyl with hle | ⟨-, hle⟩
    · omega
    · exact hle
  have hQM : Q ≤ D.M := hQsyl.le.trans inf_le_right
  have hPM : Q ⊓ X ≤ D.M := inf_le_left.trans hQM
  have hPle : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 (Q ⊓ X) :=
    CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hQXsyl.le hQXsyl le_rfl
  have hPrank : 2 ≤ CFSG.Open.pRank 3 (Q ⊓ X) := h873h.trans hPle
  obtain ⟨z, hzP, hzord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank Nat.prime_three
      (H := Q ⊓ X) (by omega)
  have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  obtain ⟨E, hzE, hEP, hEab, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
      (B := Q ⊓ X) (X := Subgroup.zpowers z) hQXsyl.isPGroup hPrank
      (Subgroup.zpowers_le.mpr hzP) hzcard
  have hEM : E ≤ D.M := hEP.trans hPM
  have hΓE : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M := by
    have hmono : CFSG.Open.rankThreeGamma 1 3 E ≤ CFSG.Open.rankThreeGamma 1 3 (Q ⊓ X) := by
      simpa [CFSG.Open.rankThreeGamma] using
        CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1) hEP
    exact hmono.trans hΓP
  have hUniqE : CFSG.LocalAnalysis.UniquenessCase.UC22.UniqueMax D.M E :=
    h63 3 (by norm_num) (by norm_num) E hEM hEab hEcard hΓE
  have hME : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_forall D.maxLocal hEM
      (fun K hK hEK => by
        have hmem : K ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := ⟨hK, hEK⟩
        rw [hUniqE] at hmem
        exact Set.mem_singleton_iff.mp hmem)
  have hEQ : E ≤ Q := hEP.trans inf_le_left
  have hMQ : Q ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hME hEQ hQM
  have hQH : Q ≤ H := hQsyl.le.trans inf_le_left
  obtain ⟨S, hQS⟩ := (hQsyl.isPGroup.comap_subtype (K := H)).exists_le_sylow
  let Sg : Subgroup G := (S : Subgroup ↥H).map H.subtype
  have hSg : CFSG.ABGLocalTools.IsSylowOf 3 Sg H := ⟨S, rfl⟩
  have hQSg : Q ≤ Sg := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQH]
    exact Subgroup.map_mono hQS
  have hsub : CFSG.Open.IsSubnormal Q Sg :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hQSg).2
      (CFSG.BaerSuzuki.Helpers.subgroup_isSubnormal_of_isPGroup hSg.isPGroup (Q.subgroupOf Sg))
  have hSgM : Sg ≤ D.M := (mem_uniqueSet_of_isSubnormal_of_mem D.maxLocal hsub hMQ).1
  have hSgHM : Sg ≤ H ⊓ D.M := le_inf hSg.le hSgM
  have hQeq : Sg = Q := CFSG.ABGLocalTools.IsSylowOf.eq_of_le hQsyl hQSg hSgHM hSg.isPGroup
  refine ⟨?_, hΓP⟩
  rw [hQeq] at hSg
  exact hSg

theorem r874_of_inputs {G : Type} [Group G] [Finite G] (D : Data G)
    (h63 : UC6.R6_3 D) (h871 : R871 D) (h873 : R873 D) : R874 D :=
  r874_of_m3 D h63 h871 (r873M3_of_r873 h873)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
