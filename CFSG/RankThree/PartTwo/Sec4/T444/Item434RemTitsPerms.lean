module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsInputs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemTits

open CFSG.Sporadic.Schreier.Tits

@[expose] noncomputable def sylPerms : List (Equiv.Perm (Fin 1755)) :=
  sylWords.map (wordIn 13 titsT)

@[expose] noncomputable def bOne : Equiv.Perm (Fin 1755) := wordIn 13 titsT bOneWord

end CFSG.RankThree.PartTwo.Sec4.Item434RemTits
