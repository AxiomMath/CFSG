module

public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfCaseA
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfCaseB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem step93OmegaCaseB_plusFour (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (h311bComm : Stroth311bCommStatement)
    (h311bCard : Stroth311bCardStatement) (h312b : Stroth312bStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
      (t r : G) (Z0 : Subgroup G) (h : G), HS9.Cfg93c hc n t r Z0 h →
      ∀ x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B), x ∉ Q → OmegaPlusFourNat hc x →
        LB M Q B ⊔ conjSubgroup h (LB M Q B) = Rt M (LB M Q B) x →
        ¬ LB M Q B ⊓ hc.CN t ≤
          inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)) → False := by
  intro G _ _ M Q Z B hc n t r Z0 h cfg x hxK hxQ hP4 _ _
  by_cases hB : Z0 ⊓ hc.CN x ≤ Q
  · exact HS9.false_of_inf_CN_le_Q h34 h311a h311bComm h311bCard cfg.hs cfg.hZ0 cfg.hsc
      (Subgroup.mem_inf.mp hxK).1 hxQ hP4 hB
  · exact HS9.false_of_not_inf_CN_le_Q_free h34 h311a h311bComm h311bCard h312b cfg hxK hxQ hP4
      hB

end CFSG.RankThree.GF2n.Stroth80
