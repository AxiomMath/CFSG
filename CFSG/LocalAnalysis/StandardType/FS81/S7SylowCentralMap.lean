module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import Certificates.Certificate8064
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)

section Row


theorem exists_sylow_central_map {G : Type} [Group G]
    (ι : adjointGroup .E8 GF₂ →* G) (hι : Function.Injective ι) :
    ∃ S : Subgroup G, IsSylow2In S ι.range ∧ ι tθ ∈ S ∧ orderOf (ι tθ) = 2 ∧
      ∀ s ∈ S, s * ι tθ = ι tθ * s := by
  obtain ⟨S_M, htM, hcentM⟩ :=
    exists_sylow_two_mem_centralizer_pinnedElt_highRoot (K := GF₂)
  refine ⟨(S_M : Subgroup (adjointGroup .E8 GF₂)).map ι, isSylow2In_map ι hι S_M,
    Subgroup.mem_map_of_mem ι htM, ?_, ?_⟩
  · rw [orderOf_injective ι hι tθ]
    exact orderOf_pinnedElt_one (highRoot .E8)
  · intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.1 hs
    calc ι s₀ * ι tθ = ι (s₀ * tθ) := (map_mul ι s₀ tθ).symm
      _ = ι (tθ * s₀) := congrArg ι (Subgroup.mem_centralizer_iff.1 hcentM s₀ hs₀)
      _ = ι tθ * ι s₀ := map_mul ι tθ s₀

end Row

end CFSG.StandardType.FrameRoute.FS81

end
