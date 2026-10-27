module

public import CFSG.Monster.B.GSide.MuFourOmega
public import Certificates.Kernel.MonsterB.Co2Mem
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphAdj
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase
public import CFSG.Monster.B.TwoA.Unitary.Twenty

public section

open CFSG.Monster.B CFSG.Monster.B.GSide CFSG.KC.Co2Mem CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3134

open CFSG.Monster.B CFSG.Monster.B.GSide CFSG.KC.Co2Mem CertificateChecks.KernelMonB

set_option maxRecDepth 100000

theorem kMem : memK 2300 24 (Co2V.F 0) 1023447 = true := by quickRfl

theorem kForm : bWcode 6144 1023447 = 1 ∧ bWcode (6144 ^^^ 31) 1023447 = 0 := by decide +kernel

end CertificateChecks.Batch3134

namespace Certificates

open CertificateChecks.Batch3134 in
open CFSG.Monster.B CFSG.Monster.B.GSide in
theorem certificate3134 : Co2.Native.vectors.contains 1023447 = true ∧ bWcode 6144 1023447 = 1 ∧
      bWcode (6144 ^^^ 31) 1023447 = 0 :=
  ⟨(vectors_contains_eq _).trans kMem, kForm⟩

end Certificates
