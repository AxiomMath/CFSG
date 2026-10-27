module

public import CFSG.GH74.GLS.Prop27.OddCoreCheck
import CFSG.Certificates.Kernel.PermCent.KGrpC2Sound
import Certificates.Kernel.PermCent.K5097
public import CFSG.GH74.KGroups.M11Inputs

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.KGrp

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.Prop27 in
open CFSG.GH74.KGroups CFSG.Certificates in
theorem certificate5097 : oddCoreCheck 495 (elemsT M11.Q) (elemsT M11.Q) = true := by
  rw [elemsT_eq_elemsC, oddCoreCheck_C]
  exact K5097.k5097

end Certificates
