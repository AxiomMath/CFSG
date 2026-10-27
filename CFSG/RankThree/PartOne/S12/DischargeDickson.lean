module

public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.SubgroupLists.DicksonGL2

public section

namespace CFSG.RankThree.PartOne

theorem extDickson : ExtDickson := fun _ _ H h =>
  CFSG.RankThree.SubgroupLists.dickson_gl_two H h

end CFSG.RankThree.PartOne
