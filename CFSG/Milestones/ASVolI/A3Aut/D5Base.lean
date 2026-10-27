module

public import CFSG.Milestones.ASVolI.A3

public section

namespace CFSG.ASVolI

theorem burnsideAut_d5_pinned_mono {S M : Type} [Group S] [Group M] {ι : S ≃* M}
    {U : Subgroup S} {F : Subgroup (MulAut S)} {P Q : MulAut M → Prop}
    (h : ChA.HasPinnedSylowFieldAction ι U F P) (hPQ : ∀ m, P m → Q m) :
    ChA.HasPinnedSylowFieldAction ι U F Q := by
  obtain ⟨Um, g, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Um, g, h1, h2, h3, hPQ g h4, h5⟩

end CFSG.ASVolI
