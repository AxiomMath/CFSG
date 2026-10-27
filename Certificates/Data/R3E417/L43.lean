module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43Mat
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res423Three

open CFSG.RankThree.PartTwo.Sec4.Item434RemL43 Matrix

@[expose] def uniMat (a b c d e f : ZMod 3) : Mat4 :=
  !![1, a, b, c; 0, 1, d, e; 0, 0, 1, f; 0, 0, 0, 1]

@[expose] def wMat (a f : ZMod 3) : Mat4 :=
  if a = 0 then rMat 0 0 0 1 else rMat 1 0 0 (f * a)

end CFSG.RankThree.PartTwo.Sec4.Res423Three
