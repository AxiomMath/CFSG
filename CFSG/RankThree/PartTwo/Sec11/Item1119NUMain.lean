module

public import CFSG.RankThree.PartTwo.Sec11.Item1119NUPart1
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUPart2
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUG2
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUD4
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUL3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymInputs

public section

namespace CFSG.RankThree.PartTwo.Sec11

section Numbers

theorem sym1119Numbers_holds (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) :
    Sym1119Numbers := by
  intro G _ _ A c L a R Y d x s r g hctx hL3n
  have hx := Item1119NU.sym1119_x_le_27 h45 h113 h117 Item1119NU.numFamG2
    Item1119NU.numFamD4 Item1119NU.numFamL3 hctx
  exact ⟨hx, Item1119NU.sym1119_r_le_9 h45 h113 h117 hx hL3n hctx⟩

end Numbers

end CFSG.RankThree.PartTwo.Sec11

end
