module

public import CFSG.Timmesfeld.Bridge.RootClosureRankOne
public import CFSG.Timmesfeld.Bridge.OddLocalRoot
public import CFSG.Timmesfeld.Bridge.OddTranspMain

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge

theorem rootGenQuotientStmt_of (h18 : CommonNeighbourStmt) : RootGenQuotientStmt := by
  intro G _ _ D hD hN d hd x hx hdx
  rcases rootGen_quotient OddTransp.oddTranspZStar h18 hD hN hd hx hdx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨hst, hd2, hx2, ho, -, -⟩ := h
    exact Or.inr (Or.inr ⟨_, _, hst, hd2, hx2, ho⟩)

end CFSG.Timmesfeld.Bridge.RootClosure
