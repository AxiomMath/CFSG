module

public import CFSG.RankThree.PartTwo.Sec4.T444.Part1Main
import CFSG.RankThree.PartTwo.Sec4.T444.Gap452Proof
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec4.Item447Proof
public import CFSG.RankThree.PartTwo.KFacts.L34CenterProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven

section Residual

variable {X : Type} [Group X] [Finite X]

theorem sectionFourHyp_quotient_pCore_two (hX : SectionFourHyp X) :
    SectionFourHyp (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (CFSG.pCore 2 X) := by
    intro p hp hp2 hdvd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X)))
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hle : ∀ p : ℕ, p.Prime → p ≠ 2 →
      localRank p (X ⧸ CFSG.pCore 2 X) ≤ localRank p X := fun p hp hp2 =>
    CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 _ (hodd p hp hp2)
  refine ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hX.kGroup ⊤ _
      (Census.quotientTopEquiv (CFSG.pCore 2 X)), ?_, ?_⟩
  · exact Census.evenRank_le_of_localRank_le fun p hp hp2 =>
      (hle p hp hp2).trans ((CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans
        hX.evenRank_le)
  · intro p hp hp3
    exact (hle p hp (by omega)).trans_lt (hX.localRank_lt p hp hp3)

theorem quasisimple_of_residual (hres : Item4_52Residual) (hX : SectionFourHyp X)
    [Group.IsPerfect X] {K : Subgroup X} [K.Normal] (hK : Group.IsSolvable K)
    (h9 : ¬ 9 ∣ Nat.card K) (ψ : X ⧸ K ≃* projSL 3 (GaloisField 2 2)) :
    IsQuasisimple (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := isSimpleGroup_projSL
  have : IsSimpleGroup (X ⧸ K) := ψ.isSimpleGroup
  have hNn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hNK : CFSG.pCore 2 X ≤ K := Census.le_of_isSolvable_of_normal hNn
    (isSolvable_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := X)))
  have hKbn : (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hKbs : Group.IsSolvable (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (CFSG.pCore 2 X)).subgroupMap_surjective K)
  have hKb9 : ¬ 9 ∣ Nat.card (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) := fun h =>
    h9 (h.trans (Subgroup.card_map_dvd _ _))
  exact hres _ (sectionFourHyp_quotient_pCore_two hX) inferInstance
    (Sec18.pCore_quotient_pCore_eq_bot 2) (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) hKbs hKb9
    ⟨(QuotientGroup.quotientQuotientEquivQuotient _ K hNK).trans ψ⟩

end Residual

section Main

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G}

theorem rank3II_4_52_of_residual
    (h434 : Item4_34Sec) (h45 : Item4_5) (hres : Item4_52Residual) : Item4_52 := by
  intro G _ _ A M h _ L hL hQL hcomm hLM
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have h3L := h.three_dvd_card_of_not_le h45 hL hLM
  have hZ := h.isZ3L34OrHeisSL34_map_starQuot h434 h45 hL hQL hcomm hLM
  obtain ⟨K, _, hKs, h9, ⟨ψ⟩⟩ := exists_solvable_quotient_projSL hA3 hL h3L hAL hZ
  have : Group.IsPerfect L := hL.1
  exact ⟨hL.1, hL.2.1,
    quasisimple_of_residual hres (sectionFourHyp_subgroup h.sectionFourHyp L) hKs h9 ψ⟩

end Main

theorem rank3II_4_44_1_of_item4_34
    (h434 : Item4_34Sec) (h45 : Item4_5) : Item4_44_1 :=
  have h452 := rank3II_4_52_of_residual h434 h45 rank3II_4_52_residual
  rank3II_4_44_1_of (rank3II_4_50_of_item4_47 (rank3II_4_47_of h45)) h452
    (rank3II_4_53_of h434 h45 h452 KFacts.l34CenterThreePrimeTwo)

end CFSG.RankThree.PartTwo.Sec4
