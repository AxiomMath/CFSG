
module

public import Certificates.Certificate15090Base

public import CFSG.Sporadic.SuzRecog.LevelTwoCheck
import Certificates.Kernel.Sporadic.L2.G7
import Certificates.Kernel.Sporadic.L2.XC
public import Mathlib

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG.Sporadic.SuzRecog in
theorem certificate15090 : LevelTwo.chainOK = true ∧ LevelTwo.basicOK = true ∧ LevelTwo.aOK = true ∧
    LevelTwo.vOK = true ∧ LevelTwo.graphOK = true ∧ LevelTwo.elimOK = true ∧
    LevelTwo.locOK = true ∧ LevelTwo.triOK = true ∧ LevelTwo.classOK = true ∧
    LevelTwo.groupOK = true :=
  ⟨L2XCG.chainOK_true, L2G.basicOK_true, L2G.aOK_k, L2G.vOK_k, L2G.graphOK_k, L2G.elimOK_k,
    L2G.locOK_true, L2G.triOK_true, L2G.classOK_true, L2G.groupOK_true⟩

end Certificates
