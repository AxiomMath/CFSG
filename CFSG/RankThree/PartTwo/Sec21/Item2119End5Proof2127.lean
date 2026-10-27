module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End5ProofPair

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item2127At : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G),
    Pair2127 G A E U c L d → ∀ F : Subgroup G, IsFOf2127 A L F →
      CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F) (Subgroup.centralizer ({c} : Set G))

theorem item2127_of_at
    (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116) (h218 : Item218)
    (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6)
    (hStar : Item2125Star) (hAt : Item2127At) : Item2127 := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 e he hed F hF
  obtain ⟨U', hP⟩ := exists_pair2127 h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar hE h23 h24 hLf
    h26 he hed
  exact hAt G A E U' e (Lf e) d hP F hF

end CFSG.RankThree.PartTwo.Sec21
