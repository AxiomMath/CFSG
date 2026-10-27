module

public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Sec
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (localRank)

namespace Item41Narrow

theorem exists_layer_section {G₀ : Type} [Group G₀] {H : Subgroup G₀} {G : Type} [Group G]
    (f : H →* G) (hf : Function.Surjective f) :
    ∃ (H₁ : Subgroup H) (g : H₁ →* layer G), Function.Surjective g ∧
      Nat.card g.ker ∣ Nat.card f.ker := by
  let H₁ : Subgroup H := (layer G).comap f
  let g : H₁ →* layer G := (f.comp H₁.subtype).codRestrict (layer G) fun x => x.2
  refine ⟨H₁, g, ?_, ?_⟩
  · rintro ⟨l, hl⟩
    obtain ⟨h, rfl⟩ := hf l
    exact ⟨⟨h, hl⟩, rfl⟩
  · rw [← Subgroup.card_map_of_injective H₁.subtype_injective]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))

theorem item434LayerRanks_of_narrow (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover) :
    Item434LayerRanks := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc
  obtain ⟨H₁, g, hg, hdvd⟩ := exists_layer_section f hf
  have hH : SectionFourHyp H :=
    ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hG₀.kGroup H ⊥ QuotientGroup.quotientBot,
      (evenRank_subgroup_le H).trans hG₀.evenRank_le,
      fun p hp h3 => (localRank_subgroup_le hp H).trans_lt (hG₀.localRank_lt p hp h3)⟩
  have e : H₁ ⧸ g.ker ≃* layer G := QuotientGroup.quotientKerEquivOfSurjective g hg
  have hq := hc.isQuasisimple
  have hE : SectionFourHyp (layer G) :=
    Census.sectionFourHyp_of_mulEquiv e (sectionFourHyp_section h1 hH H₁ g.ker
      (fun h => hker (h.trans hdvd)) (isQuasisimple_of_mulEquiv e.symm hq))
  have hZ := hc.isPGroup_center_layer
  exact ⟨fun p hp hp3 _ => (localRank_quotient_center_le hZ hp hp3).trans_lt
    (hE.localRank_lt p hp hp3), fun hZ1 => h2 _ hE hq hZ hZ1⟩

end Item41Narrow

end CFSG.RankThree.PartTwo.Sec4
