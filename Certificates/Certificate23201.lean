module

public import Certificates.Data.FooteLitCF23L216Check
import CFSG.Certificates.Kernel.PermCent.L216SylSound
import Certificates.Kernel.PermCent.K23201
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG.Certificates.Kernel.PkCV.L216S

namespace Certificates

open CFSG.ComponentClassification.GSThmB.CF23I.L216 in
theorem certificate23201 : l216CosetOK = true :=
  CFSG.KC.L216Syl.l216CosetOK_of K23201.kSift K23201.kComm K23201.kLen K23201.kNodup
    K23201.kStable K23201.kCov

end Certificates
