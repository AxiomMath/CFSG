module

public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.A1bPGroups

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem kGroup_of_ne_top (hK : quasithinIsQTKECat G) {H : Subgroup G}
    (hH : H ≠ ⊤) : CFSG.SectionRank.IsKGroupCat H :=
  CFSG.QuasithinUnique.isKGroupCat_of_kProper hK.1 hH

theorem pRank_le_two_of_isTwoLocal (hK : quasithinIsQTKECat G)
    {H : Subgroup G} (hH : IsTwoLocal H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p H ≤ 2 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 H hH).trans hK.2.2

theorem pRank_le_two_of_pCoreOf_ne_bot (hK : quasithinIsQTKECat G)
    {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p H ≤ 2 := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hH, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)).trans
      (pRank_le_two_of_isTwoLocal hK hloc hp hp2)

theorem stronglyQuasithin_of_pCoreOf_ne_bot (hK : quasithinIsQTKECat G)
    {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) : CFSG.Open.SQTKTauCeti.StronglyQuasithin H := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have h := pRank_top_subtype (p := p) H
  change CFSG.Open.pRank p (⊤ : Subgroup H) ≤ 2
  rw [h]
  exact pRank_le_two_of_pCoreOf_ne_bot hK hH hp hp2

theorem kGroup_of_pCoreOf_ne_bot (hK : quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) : CFSG.SectionRank.IsKGroupCat H :=
  haveI := hs
  kGroup_of_ne_top hK (CFSG.QuasithinUnique.ne_top_of_pCoreOf_ne_bot_of_simple hnab hH)

end CFSG.Quasithin
