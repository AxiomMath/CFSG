module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJoin

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRankOnePerf_comm_of_nbr
    (hL1 : GGSecFiveL1CoxInput) (hRk2 : GGSecFiveRk2Input)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {y : G} {K : Subgroup G}
    (hK : GGNbr p B x D J y K)
    (hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    {r r' : MulAut ↥Bs} (hr : r ∈ ggAutomizer K Bs) (hrC : r ∈ ggCoxRefl M e)
    (hr' : r' ∈ ggAutomizer K Bs) (hr'C : r' ∈ ggCoxRefl M e) (hne : r ≠ r')
    (hcomm : r * r' = r' * r) :
    ∀ a ∈ ggRankOnePerf Bs r, ∀ b ∈ ggRankOnePerf Bs r', a * b = b * a := by
  obtain ⟨hcfg', heq⟩ := ggSecFiveRouteCfg_singleton hcfg hK hle
  let e' : M.Group ≃* ↥(ggAutomizerJoin L Bs {K}) := e.trans (MulEquiv.subgroupCongr heq.symm)
  have he' : ∀ g, ((e' g : ↥(ggAutomizerJoin L Bs {K})) : MulAut ↥Bs) =
      ((e g : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := fun g =>
    MulEquiv.subgroupCongr_apply heq.symm (e g)
  have hpres' : GGCoxeterPres p (ggAutomizerJoin L Bs {K}) M e' := by
    refine ⟨hpres.1, fun i => ?_⟩
    rw [he']
    exact hpres.2 i
  have hC : ∀ s ∈ ggCoxRefl M e, s ∈ ggCoxRefl M e' := by
    rintro s ⟨w, i, rfl⟩
    exact ⟨w, i, (he' _).symm⟩
  have hKm : K = L ∨ K ∈ ({K} : Finset (Subgroup G)) := Or.inr (Finset.mem_singleton_self K)
  have h1 := hL1 G p B Bs x L D J {K} hcfg' hsplit ι M e' hpres' hle3 K hKm
  have hcl := (hRk2 G p B Bs x L D J {K} hcfg' hsplit ι M e' hpres' hle3 K hKm r hr (hC r hrC)
    r' hr' (hC r' hr'C) hne).1 hcomm
  intro a ha b hb
  rw [h1 r hr (hC r hrC)] at ha
  rw [h1 r' hr' (hC r' hr'C)] at hb
  exact hcl a ha b hb

end CFSG.StandardType

end
