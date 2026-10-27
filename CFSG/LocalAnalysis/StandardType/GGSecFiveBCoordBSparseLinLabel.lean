module

public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGHalfJoinAutNarrow
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem card_ggAutomizer_of_e6Two_nbr {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hNoTr : GGNoTransvection 3 Bs)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs K)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ 3) :
    Nat.card ↥(ggAutomizer K Bs) = 1152 :=
  card_ggAutomizer_of_e6Two_of_rank hcfg hNoTr hK
    (fun θ hN hperf => pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hperf θ hN) hZ

end CFSG.StandardType
