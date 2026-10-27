module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517One
public import CFSG.Quasithin.Background.B610TwoMain

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank

theorem stmt5_1_7_one_nat_of_two (h610 : B610Two) (hR : L2RankOneSylowFact) :
    Stmt5_1_7_one_nat := by
  intro G _ _ T M L V n h hV hJ hnq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hchar : CharTwo (L ⊔ T) :=
    charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, h.maximal.1.2.2.2⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hnat := isNaturalL2Prime_of_isNatQuotCh5 (by have := h.two_le; omega) hnq
  have hS := h610 G (L ⊔ T) T _ V L n (h.minParabolic_sup hR) hchar hred le_sup_left
    h.sup_le_normalizer rfl h.faithful.2.1 (h.inf_centralizer_le hLV hV.2.2) h.two_le hnat hJ
  have hnorm : baum T ⊔ L ≤ Subgroup.normalizer (L : Set G) :=
    sup_le ((inf_le_left : baum T ≤ T).trans h.T_le_normalizer) Subgroup.le_normalizer
  exact A4.isSylowTwoOf_inf_normal hS le_sup_right hnorm

theorem stmt5_1_7_one_nat_of_rankOne (hR : L2RankOneSylowFact) : Stmt5_1_7_one_nat :=
  stmt5_1_7_one_nat_of_two B610T.b610Two_holds hR

end CFSG.Quasithin.H13

end
