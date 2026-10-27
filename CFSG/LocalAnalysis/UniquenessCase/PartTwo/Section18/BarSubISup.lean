module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Vol2.Ch5Sec1HallE22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

variable {G : Type} [Group G] {ι : Sort*}

theorem barSub_iSup_of_le {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : ι → Subgroup G} (hK : ∀ i, K i ≤ stabTil V₀ V) :
    barSub V₀ V hV (⨆ i, K i) = ⨆ i, barSub V₀ V hV (K i) := by
  unfold barSub
  rw [CFSG.Quasithin.H13.subgroupOf_iSup_of_le (H := stabTil V₀ V) K hK, Subgroup.map_iSup]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
