module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemmaH4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2_exists_movesLine_refl_M {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hTBN : GGQ2TableBNbr) (hS : GGQTwoSetting 3 B Bs x L D J)
    (hI1 : ¬ GGQTwoI1 Bs D J) :
    ∃ ρ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs,
      GGIsReflection 3 ρ ∧ GGQ2MovesLine Bs x ρ := by
  obtain ⟨y, K, hnb⟩ := exists_ggNbr hS.1.1.1.2.2.2.2.2.2.2 hS.1.1.2.2
  obtain ⟨M, h3⟩ := hTBN hS rfl hI1 hnb
  obtain ⟨ρ, hρ, hR, hmv⟩ := ggQ2_lemmaH4 rfl hS hnb M h3
  exact ⟨ρ, ggAutomizer_mono Bs ((le_ggG0_of_ggNbr hnb).trans Subgroup.le_normalizer) hρ, hR, hmv⟩

end CFSG.StandardType

end
