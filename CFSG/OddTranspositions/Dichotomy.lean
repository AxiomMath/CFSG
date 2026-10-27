module

public import CFSG.OddTranspositions.F3NoSqE1
public import CFSG.OddTranspositions.ThreeTranspositionAssembly
public import CFSG.OddTranspositions.ThreeTranspositions
public import CFSG.OddTranspositions.Assembly

public section

namespace CFSG.OddTranspositions

theorem threeTranspositionDichotomy :
    ThreeTranspositionDichotomy :=
  threeTranspositionDichotomy_of_f3Row f3Row

theorem ascNoSqDichotomy
    (hI1 : NoSqE1OrThreeTranspositions) :
    AscNoSqDichotomy :=
  ascNoSqDichotomy_of_inputs hI1
    (fun G _ _ D hcls hinv hprod hgen hcenter hsolv hEG =>
      commutator_isSimpleGroup_of_threeTranspositions hcls hinv hprod hgen hcenter hsolv hEG)
    threeTranspositionDichotomy

end CFSG.OddTranspositions
