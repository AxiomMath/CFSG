module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1EDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1LeviE

public section

namespace CFSG.StandardType

section IdentE

theorem ggSecFiveLeviE_of_tier1 (hT : GGSecFiveTier1Input) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M) :
    GGLeviPresented (L ⊔ ⨆ K ∈ 𝒦, K)
      (fun i : ι => ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
  rcases hE with ⟨e', hM⟩ | ⟨e', hM⟩ | ⟨e', hM⟩
  · exact ggSecFiveLeviE6_of_tier1 hT hcfg hsplit hpres e' hM
  · exact ggSecFiveLeviE7_of_tier1 hT hcfg hsplit hpres e' hM
  · exact ggSecFiveLeviE8_of_tier1 hT hcfg hsplit hpres e' hM

theorem ggSecFiveIdentEInput_of_tier1 (hT : GGSecFiveTier1Input) : GGSecFiveIdentEInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hE
  exact (ggSecFiveLeviE_of_tier1 hT hcfg hsplit hpres hE).ident

theorem ggSecFiveIdentCompatEInput_of_tier1 (hT : GGSecFiveTier1Input)
    (hC : GGSecFiveCompatLeviInput) : GGSecFiveIdentCompatEInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hE
  exact (ggSecFiveLeviE_of_tier1 hT hcfg hsplit hpres hE).compat hC hcfg hsplit hpres (Or.inr hE)

end IdentE

end CFSG.StandardType

end
