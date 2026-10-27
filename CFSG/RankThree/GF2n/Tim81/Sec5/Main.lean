module

public import CFSG.RankThree.GF2n.Tim81.Sections4to7
import CFSG.RankThree.GF2n.Tim81.Sec5.S56Rank
import CFSG.RankThree.GF2n.Tim81.Sec5.S56Split
import CFSG.RankThree.GF2n.Tim81.Sec5.S57
import CFSG.RankThree.GF2n.Tim81.Sec5.S58
import CFSG.RankThree.GF2n.Tim81.Sec5.S512
import CFSG.RankThree.GF2n.Tim81.Sec5.S513

public section

namespace CFSG.RankThree.GF2n.Tim81

theorem sec5Results (G : Type) [Group G] [Finite G] :
    Sec5Results G := by
  have h56 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt56 M V :=
    fun M V hS => hS.stmt56_of_stmt56a hS.stmt56a
  have h57 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt57 M V :=
    fun M V hS => hS.stmt57 h56
  have h58 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt58 M V :=
    fun M V hS => hS.stmt58 (h57 M V hS)
  have h512 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt512 M V :=
    fun M V hS => hS.stmt512 h57 h58
  have h513 : ∀ M V : Subgroup G, Sec5Hyp M V → Sec5.Stmt513 M V :=
    fun M V hS => hS.stmt513 h57 h512
  exact
    { s53 := fun M V hS => hS.stmt53
      s54 := fun M V hS => hS.stmt54
      s55 := fun M V hS => hS.stmt55
      s55e := fun M V hS => hS.stmt55e
      s56 := h56
      s57 := h57
      s58 := h58
      s512 := h512
      s513 := h513
      i5a := fun M V hS => hS.toRootHyp.stmtI5a
      i5b := fun M V hS => hS.toRootHyp.stmtI5b }

theorem sec5ResultsStatement : Sec5ResultsStatement := by
  intro G _ _
  exact sec5Results G

end CFSG.RankThree.GF2n.Tim81
