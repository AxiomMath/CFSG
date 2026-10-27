module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res12ProofKO3Layer
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsYKO3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

theorem simple_three_dvd_small {K : Type} [Group K] [Finite K]
    (htype : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 1)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 2))) :
    IsSimpleGroup (K ⧸ CFSG.pCore 2 K) ∧ 3 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
  rcases htype with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · haveI := CFSG.RankThree.PartTwo.Sec21.Item222Proof.isSimpleGroup_projSL_three
      (GaloisField 2 1)
    exact ⟨e.isSimpleGroup, CFSG.RankThree.PartTwo.KFacts.three_dvd_card_of_mulEquiv_projSL e⟩
  · haveI := CFSG.RankThree.PartTwo.Sec21.isSimpleGroup_projSL_two (m := 2) (by norm_num)
    exact ⟨e.isSimpleGroup, CFSG.RankThree.PartTwo.Sec21.three_dvd_card_of_mulEquiv_projSL e⟩

theorem kO3CentLayer_small
    {G : Type} [Group G] [Finite G] (hKP : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    {K O : Subgroup G} (hO : O ≠ ⊤) (hperf : Group.IsPerfect K)
    (htype : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 1)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 2)))
    (hKN : K ≤ Subgroup.normalizer (O : Set G)) (h3 : Nat.Coprime 3 (Nat.card O))
    (hrank : ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p O ≤ 2) :
    ∀ k ∈ K, ∀ o ∈ oTwoLayer O, k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O := by
  intro k hk o ho
  obtain ⟨x, hx, rfl⟩ := ho
  have hOK : CFSG.IsKGroup ↥O :=
    (KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant hKP O hO).kGroupAllSimple
      CFSG.Assembly.inCatalog_isoInvariant CFSG.Assembly.inCatalog_containsAbelianSimple
  have hKX : CFSG.IsKGroup (↥O ⧸ CFSG.pCore 2 O) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hOK (CFSG.pCore 2 O)
  have h3X : ¬ 3 ∣ Nat.card (↥O ⧸ CFSG.pCore 2 O) := fun hd =>
    absurd (Nat.eq_one_of_dvd_coprimes h3 (dvd_refl (3 : ℕ))
      (hd.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 O)))) (by norm_num)
  have hrank5 : CFSG.Open.pRank 5 (⊤ : Subgroup (↥O ⧸ CFSG.pCore 2 O)) ≤ 2 := by
    have h5 := (Res11.pRank_quotient_le O (p := 5) (by norm_num) (by norm_num)).trans
      (hrank 5 (by norm_num) (le_refl 5))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h5
    exact h5
  obtain ⟨hS, h3K⟩ := simple_three_dvd_small htype
  have hS3 : ∀ (H : Type) [Group H] (f : ↥K →* H), ¬ 3 ∣ Nat.card f.range → f.range = ⊥ :=
    fun H _ f hf => CFSG.RankThree.PartTwo.Sec16.Res6Act.range_eq_bot_of_not_three_dvd_pCore
      hperf hS h3K f hf
  have hfixE : ∀ (k' : K), ∀ y ∈ CFSG.layer (↥O ⧸ CFSG.pCore 2 O),
      Res11.quotAction hKN k' y = y := by
    intro k' y hy
    have hle : CFSG.layer (↥O ⧸ CFSG.pCore 2 O) ≤
        RankThree.PartOne.FixedRank36.fixedSub (Res11.quotAction hKN k') :=
      sSup_le fun J hJ z hz =>
        CFSG.RankThree.PartTwo.Sec16.Res6Act.fix_component_of_perfect_three hperf hS3
          (Res11.quotAction hKN) hKX h3X hrank5 hJ k' hz
    exact hle hy
  have hfix : Res11.quotAction hKN (⟨k, hk⟩ : K) (QuotientGroup.mk' (CFSG.pCore 2 O) x) =
      QuotientGroup.mk' (CFSG.pCore 2 O) x :=
    hfixE ⟨k, hk⟩ (QuotientGroup.mk' (CFSG.pCore 2 O) x) hx
  exact Res11.comm_mem_of_quotAction_fix hKN ⟨k, hk⟩ x hfix

end CFSG.RankThree.PartTwo.Sec20.SimsYKO3
