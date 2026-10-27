module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenGlue
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenLarge

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

theorem evenSL3Irred :
    EvenSL3Irred :=
  evenSL3Irred_of_nondeg (evenSL3IrredNondeg_of_large evenSL3IrredLarge)


theorem inspectSig148L3Loc : InspectSig148L3Loc :=
  inspectSig148L3Loc_of_list
      (evenSimpleList_of_L3
          (evenSimpleListL3_of_irred
              (evenSL3Irred_of_nondeg (evenSL3IrredNondeg_of_large evenSL3IrredLarge))))

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
