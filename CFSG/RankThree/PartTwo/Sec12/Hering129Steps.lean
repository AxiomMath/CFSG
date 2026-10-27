module

public import CFSG.RankThree.PartTwo.Sec12.Hering129Setup
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem false_of_hj_omega (h128 : Item128BarAt) {A L K S : Subgroup G} {c b a : G}
    (cfg : Cfg129 G A c L b a K S) (hAT : A ∉ partTwoT G)
    (hΩ : ¬ StarConditionAt A (a * b)) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hxL, hxB, hxA, hx1⟩ := cfg.point_facts
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1
  have hxΩ : Subgroup.zpowers (a * b) ∈ Sec13.omegaA A :=
    Sec13.zpowers_mem_omegaA_iff.mpr ⟨hxA, Sec13.card_zpowers_eq_three hAe hxA hx1, hΩ⟩
  have h := (h128 G A c L cfg.std cfg.mem_E cfg.list).resolve_left hAT (a * b) hxΩ
  rcases h.1 with ⟨hB, -⟩ | ⟨hL, -⟩
  · exact hxB hB
  · exact hxL hL

end CFSG.RankThree.PartTwo.Sec12
