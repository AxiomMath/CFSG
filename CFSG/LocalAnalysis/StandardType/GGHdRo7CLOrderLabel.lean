module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_lorder_label_exists {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨-, lab, hlab, hraw⟩ := hH.2.2.1.1
  exact ⟨lab, hlab,
    largeEvenRawDatum_mono (fun R _ I F h => by obtain ⟨θ, -⟩ := h.2.2; exact ⟨θ⟩) hraw⟩

end CFSG.StandardType.HdRo7C

end
