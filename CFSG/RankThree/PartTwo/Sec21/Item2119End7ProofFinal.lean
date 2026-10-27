module

public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)


variable {G : Type} [Group G] [Finite G]

namespace Item2119End7Proof

theorem mem_a_not_mem {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) : a ∈ A ∧ a ∉ Subgroup.zpowers d :=
  ⟨hE.cfg.pair.mem_E.2 hE.mem_a.1, fun h =>
    Item2119EndProof.not_mem_sup_of_config2119End hE (Subgroup.mem_sup_right h)⟩

end Item2119End7Proof

end CFSG.RankThree.PartTwo.Sec21
