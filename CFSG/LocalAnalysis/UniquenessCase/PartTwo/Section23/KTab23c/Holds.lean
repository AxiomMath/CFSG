module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kTab23c_holds : KTab23c :=
  KTabC.kTab23c_of_sylowFixedLine (fun K _ _ _ b c hirr => KTabC.sylowFixedLine_minus K b c hirr)
    (fun K _ _ _ hK => KTabC.sylowFixedLine_plus K hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
