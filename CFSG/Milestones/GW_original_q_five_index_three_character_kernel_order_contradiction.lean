module

public import CFSG.Blueprint.DihedralRefinements
public import CFSG.Dihedral.OriginalCharacterKernel

public section

namespace CFSG.Milestones

open DihedralBlueprint

theorem gw_original_q_five_index_three_character_kernel_order_contradiction (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (d : OriginalData G)
    (hs : d.Stationarity) (hc : d.CanonicalNormalizers) (hm : d.MaximalOddKernel)
    (hp : d.PureProjectiveNormalizer) (hb : d.CosetBounds)
    (hn : d.n = 3) (hR : d.R ≠ ⊥) (hCN : d.C < d.N)
    (w : CoordinateWitness (d.N ⧸ CFSG.Assembly.oddCore d.N)) (hq : Nat.card w.K = 5)
    (hindex : (d.commonE.subgroupOf d.R).index = 3) (horder : d.ConditionalOrder) : d.CharacterKernelConclusion := by
  clear hs hc hm hb hCN horder
  exact (d.q_five_index_three_impossible hnonab hp hn hR w hq hindex).elim

end CFSG.Milestones

namespace CFSG.Milestones

open DihedralBlueprint

theorem gw_original_q_five_index_three_character_kernel_order_contradiction_full (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (d : OriginalData G)
    (hs : d.Stationarity) (hc : d.CanonicalNormalizers) (hm : d.MaximalOddKernel)
    (hp : d.PureProjectiveNormalizer) (hb : d.CosetBounds)
    (hn : d.n = 3) (hR : d.R ≠ ⊥) (hCN : d.C < d.N)
    (w : CoordinateWitness (d.N ⧸ CFSG.Assembly.oddCore d.N)) (hq : Nat.card w.K = 5)
    (hindex : (d.commonE.subgroupOf d.R).index = 3) (horder : d.ConditionalOrderFull) : d.CharacterKernelConclusion := by
  exact gw_original_q_five_index_three_character_kernel_order_contradiction G hnonab d
    hs hc hm hp hb hn hR hCN w hq hindex horder.1

end CFSG.Milestones
