module

public import CFSG.RankThree.GF2n.Stroth80.CarterSec93OmegaHalfA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank


@[expose] def Step93OmegaCaseBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (Z0 : Subgroup G) (h : G), HS9.Cfg93c hc n t r Z0 h →
    ∀ x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B), x ∉ Q →
      LB M Q B ⊔ conjSubgroup h (LB M Q B) = Rt M (LB M Q B) x →
      ¬ LB M Q B ⊓ hc.CN t ≤
        inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)) → False

theorem step93OmegaCase_of_caseB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    (hB : Step93OmegaCaseBStatement) : Step93OmegaCaseStatement := by
  intro G _ _ M Q Z B hc n t r Z0 h cfg x hxK hxQ hR
  by_cases hLN : LB M Q B ⊓ hc.CN t ≤
      inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B))
  · exact step93OmegaCase_of_le_pCore h34 h311a h311bComm h312b G M Q Z B hc n t r Z0 h cfg x
      hxK hxQ hR hLN
  · exact hB G M Q Z B hc n t r Z0 h cfg x hxK hxQ hR hLN

end CFSG.RankThree.GF2n.Stroth80
