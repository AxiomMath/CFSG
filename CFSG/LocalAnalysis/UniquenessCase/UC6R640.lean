module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.CGT.PushingUpLit.NineChoiceJ
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeK
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.RankThree.PartOne.LIT.KFCGTList

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.CGT.PushingUpLit CFSG.RankThree.PartOne CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r6_40_1_of_inputs (u1 : AschbacherTheoremOneK) (u2 : AschbacherTheoremTwoK)
    (s25 : SolomonAlternatingBlockK) (D : Data G) : R6_40_1 D := by
  intro N hN L hL
  have hLN : L.map N.subtype ≤ N := Subgroup.map_subtype_le L
  have hsub : (L.map N.subtype).subgroupOf N = L :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective L
  have hblock : CFSG.CGT.PushingUp.IsBlockOfInX N (L.map N.subtype) :=
    (isBlockInX_subgroupOf_iff hLN).1 (by rw [hsub]; exact hL)
  have hΩ : CFSG.CGT.PushingUp.InOmega (L.map N.subtype) :=
    ⟨hblock.2.2, N, isMaximalTwoLocal_of_rankThreeIsMaxTwoLocal hN, hLN, hblock.2.1⟩
  have hle := CFSG.AGLEmbedding.NoXBlock.evenRank_le_two_of_inOmegaK u1 u2 s25
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp D.standing.kProper)
    D.standing.simple
    (CFSG.AGLEmbedding.NoXBlock.assembly_isCharTwoType_of_open D.standing.charTwo) hΩ
  have h3 := D.standing.rank
  have h4 := CFSG.AGLEmbedding.NoXBlock.open_evenRank_eq (G := G)
  omega

theorem r6_40_2_of_pushingUp (hPU : PushingUpCorollaryΩ) (D : Data G) : R6_40_2 D := by
  haveI := D.standing.simple
  have hK := CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp
    D.standing.kProper
  have hchar := CFSG.AGLEmbedding.NoXBlock.assembly_isCharTwoType_of_open D.standing.charTwo
  have he : 3 ≤ CFSG.Assembly.evenRank G := D.standing.rank
  obtain ⟨T', hT'⟩ : ∃ P : Sylow 2 G, (P : Subgroup G) = D.T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hP, hdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff (G := G) (p := 2) (P := D.T)
      (K := ⊤)).1 (by convert D.sylowG)
    rw [Subgroup.relIndex_top_right] at hdvd
    exact ⟨hP.toSylow hdvd, rfl⟩
  have hT1 : D.T ≠ ⊥ := ne_bot_of_isSylowOf_two D.maxLocal.1 D.sylowM
  have hStar : characteristicCoreStar D.T = ⊤ := by
    by_contra hne
    have hne' : characteristicCoreStar (T' : Subgroup G) ≠ ⊤ := by rw [hT']; exact hne
    rcases hPU G hK hchar T' (characteristicCoreStar (T' : Subgroup G)) hne'
      (fun T₁ h1 h2 h3 => normalizer_le_characteristicCoreStar h1 h2 h3)
      (centralizer_le_characteristicCoreStar _) with h | h | h
    · exact absurd (kfCGTList G hchar (Or.inl h)) (by omega)
    · exact absurd (kfCGTList G hchar (Or.inr h)) (by omega)
    · exact absurd (evenRank_le_two_of_sectionalTwoRankLEFour hchar h) (by omega)
  have hZ1 : omegaOneCenterIn D.T ≠ ⊥ :=
    Sec15Final.omegaOneCenterIn_ne_bot D.sylowM.isPGroup hT1
  have hle1 : characteristicCoreStar D.T ≤ calCGS D.T := by
    refine characteristicCoreStar_le ?_ ?_
    · exact (Subgroup.centralizer_le_normalizer _).trans
        (le_iSup_of_le (omegaOneCenterIn D.T) (le_iSup_of_le hZ1
          (le_iSup_of_le (Sec15Final.omegaOneCenterIn_le D.T)
            (le_iSup_of_le (omegaOneCenterIn_characteristic D.T) le_rfl))))
    · intro B hB1 hBS hBc
      exact le_iSup_of_le B (le_iSup_of_le hB1
        (le_iSup_of_le (hBS.trans (Sec15Final.pushingUpS_le D.T))
          (le_iSup_of_le (CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans
            (Sec15Final.pushingUpS_le D.T) hBS (CFSG.CGT.PushingUp.characteristic_pushingUpS D.T)
            hBc) le_rfl)))
  have hle2 : characteristicCoreStar D.T ≤
      calCGS (pushingUpS D.T) ⊔ centralizer (omegaOneCenterIn D.T : Set G) := by
    refine characteristicCoreStar_le le_sup_right ?_
    intro B hB1 hBS hBc
    exact le_sup_of_le_left (le_iSup_of_le B (le_iSup_of_le hB1
      (le_iSup_of_le hBS (le_iSup_of_le hBc le_rfl))))
  rw [hStar] at hle1 hle2
  exact ⟨top_le_iff.1 hle1, (top_le_iff.1 hle2).symm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6
