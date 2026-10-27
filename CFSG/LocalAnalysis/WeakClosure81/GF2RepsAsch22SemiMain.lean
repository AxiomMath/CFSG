module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22SemiCenter
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22SemiFree

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem pRank_le_three_of_layer_eq_top (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3) (H : Subgroup G)
    {S : Type} [Group S] [Finite S] (π : H →* S) (hπ : Function.Surjective π)
    (hE : CFSG.layer S = ⊤) : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 3 := by
  classical
  have hSperf : Group.IsPerfect S :=
    Group.IsPerfect.top_iff.mp (hE ▸ CFSG.LocalCores.layer_isPerfect)
  have hZ : ¬ p ∣ Nat.card (Subgroup.center S) :=
    not_dvd_card_center_of_layer_eq_top hC5 hK hp hp5 hrk H π hπ hE
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S))
      = CFSG.Open.pRank p (⊤ : Subgroup S) := by
    have : Fact p.Prime := ⟨hp⟩
    exact CFSG.SectionRank.pRank_quotient_eq (Subgroup.center S) hZ
  have hElayer : CFSG.layer (S ⧸ Subgroup.center S) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hE (QuotientGroup.mk' (Subgroup.center S))
      (QuotientGroup.mk'_surjective _)
  have hZq : Subgroup.center (S ⧸ Subgroup.center S) = ⊥ :=
    @Group.IsPerfect.center_quotient_center_eq_bot S _ hSperf
  have hπq : Function.Surjective
      ((QuotientGroup.mk' (Subgroup.center S)).comp π) :=
    (QuotientGroup.mk'_surjective _).comp hπ
  have hle := pRank_le_three_of_center_eq_bot hC5 hK hp hp5 hrk H
    ((QuotientGroup.mk' (Subgroup.center S)).comp π) hπq hElayer hZq
  rwa [hquot] at hle

end CFSG.LocalAnalysis.WeakClosure81.Asch22
