module

public import CFSG.RankThree.GF2n.Stroth80.Sec84Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec86Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec85Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec84Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec84Leaves : Prop where
  h51 : Stroth51Statement
  h82 : Stroth82Statement
  h83 : Stroth83Statement
  hNt : StrothNtStatement
  aExists : Sec8AExistsStatement
  ti : Sec8TIStatement
  zt : Sec8ZtStatement
  h56 : Stroth56SpStatement
  minOrder : Sec86MinOrderStatement
  normH : Sec86NormHStatement
  case1 : Step84CaseOneStatement
  case2 : Step84CaseTwoStatement
  f2 : Step85F2Statement
  firstV : Step85FirstVStatement
  comm : Step85CommStatement
  sylow : Step85SylowStatement
  tim81 : Tim81StrothSpStatement
  hypSub : Step86HypSubStatement
  notUnitary : Step86NotUnitaryStatement

theorem sec84_of_leaves (L : Sec84Leaves) :
    Stroth84Statement ∧ Stroth85Statement ∧ Stroth86Statement := by
  have hConj : Sec86ConjStatement := sec86Conj_of_parts L.h56 L.zt L.h51 L.aExists
  have hCN : Step85CNNormalStatement := step85CNNormal_of_zt L.zt L.h51 L.aExists L.hNt
  have hFirst : Step85FirstStatement :=
    step85First_of_parts L.zt L.h51 L.aExists L.hNt L.firstV
  have h84 : Stroth84Statement :=
    stroth84_of_cases L.h82 L.h83 hConj L.case1 L.case2
  have hO2 : Step85O2Statement :=
    step85O2_of_parts h84 L.aExists hCN hFirst L.comm L.sylow
  have h85 : Stroth85Statement := stroth85_of_steps L.f2 hO2
  have hirr : Sec86IrredStatement :=
    sec86Irred_of_inputs L.h83 L.h51 L.aExists L.minOrder
  have hNL : Sec86NormLBStatement := sec86NormLB_of_82 L.h82 hConj L.normH
  exact ⟨h84, h85,
    stroth86_of_inputs h84 h85 hirr L.ti hNL L.tim81 L.hypSub L.notUnitary⟩

end CFSG.RankThree.GF2n.Stroth80
