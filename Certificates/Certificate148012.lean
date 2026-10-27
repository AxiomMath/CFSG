module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RG24Data
import Certificates.Kernel.Ronan148.G24P0Facts

public section

namespace Certificates

open CFSG.LieType.Multipliers.G24 CFSG.RankThree.PartTwo.Sec4.Ronan148R.G24P in
theorem certificate148012 : toMat 14 (p1Arr ()) ^ 3 = 1 ∧ toMat 14 (p2Arr ()) ^ 3 = 1 ∧
    toMat 14 (p1Arr ()) * toMat 14 (p2Arr ()) * toMat 14 (p1Arr ()) ^ 2 *
      toMat 14 (p2Arr ()) ^ 2 = toMat 14 (z0Arr ()) ∧
    toMat 14 (z0Arr ()) * toMat 14 (p1Arr ()) = toMat 14 (p1Arr ()) * toMat 14 (z0Arr ()) ∧
    toMat 14 (z0Arr ()) * toMat 14 (p2Arr ()) = toMat 14 (p2Arr ()) * toMat 14 (z0Arr ()) ∧
    toMat 14 (z0Arr ()) ≠ 1 := CFSG.KD.Ronan148.G24P0.facts

end Certificates
