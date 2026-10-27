module

public import CFSG.RankThree.PartTwo.Sec13.Item135
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCenter

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item135A7Z3HypT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypT A → c ∈ L → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) → False

theorem item135A7Z3_of (hT : Item135A7Z3HypT) : Item135A7Z3 := by
  intro G _ _ A c L hD hST hnq hO2 hm hO hA7
  have hcL : c ∈ L := ResProof.mem_of_three_dvd_card_center hD (by rw [hA7.1])
  rcases hST with hS | hT'
  · exact ResProof.not_mem_of_hypS hD hS hcL
  · exact hT G A c L hD hT' hcL hnq hO2 hm hO hA7

end CFSG.RankThree.PartTwo.Sec13
