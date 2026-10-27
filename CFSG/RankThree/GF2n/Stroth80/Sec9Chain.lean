module

public import CFSG.RankThree.GF2n.Stroth80.Sec94
public import CFSG.RankThree.GF2n.Stroth80.Sec92Quot
public import CFSG.RankThree.GF2n.Stroth80.Sec9NComm
public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

structure Sec9OpenStatements : Prop where
  hA : Sec9AExistsStatement
  hn5 : Sec9NGeFiveStatement
  s91a : Step91OrderQBStatement
  s91b : Step91OrderVQBStatement
  s91c : Step91InterStatement
  s91d : Step91MixedCommStatement
  s92s : Step92SplitStatement
  s93a : Step93OneStatement
  s93b : Step93VanishStatement
  s93c : Step93TIStatement
  s93d : Step93FourStatement
  s93e : Step93EndStatement
  s93f : Close93FinalWithClaimThreeStatement
  s94a : Step94ConjVStatement
  s94b : Step94NSixStatement
  s94c : Step94EndStatement

theorem stroth91_of_open (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311b : Stroth311bCommStatement) (S : Sec9OpenStatements) : Stroth91Statement :=
  ⟨stroth91a, stroth91b_of_steps h34 h311a (sec9NComm_of_311b h34 h311b) S.s91a S.s91b S.s91c
    S.s91d, stroth91c_of_34 h34⟩

theorem stroth92_of_open (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311b : Stroth311bCommStatement) (S : Sec9OpenStatements) : Stroth92Statement :=
  stroth92_of_steps S.hA (stroth91_of_open h34 h311a h311b S).2.1
    (step92Nontriv_of h34 S.hA (stroth91_of_open h34 h311a h311b S).2.1 S.hn5 S.s91a S.s91b)
    step92Quot S.s92s

theorem stroth93_of_open (S : Sec9OpenStatements) : Stroth93Statement :=
  stroth93_of_steps_withClaimThree S.hA S.s93a S.s93b S.s93c S.s93d S.s93e S.s93f

theorem stroth94_of_open (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311b : Stroth311bCommStatement) (S : Sec9OpenStatements) : Stroth94Statement :=
  stroth94_of_steps (stroth93_of_open S) (stroth92_of_open h34 h311a h311b S) S.s94a S.s94b S.s94c

theorem stroth9_of_open (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311b : Stroth311bCommStatement) (S : Sec9OpenStatements) :
    Stroth91Statement ∧ Stroth92Statement ∧ Stroth93Statement ∧ Stroth94Statement :=
  ⟨stroth91_of_open h34 h311a h311b S, stroth92_of_open h34 h311a h311b S, stroth93_of_open S,
    stroth94_of_open h34 h311a h311b S⟩

end CFSG.RankThree.GF2n.Stroth80
