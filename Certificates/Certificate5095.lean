module

public import CFSG.GH74.GLS.Prop27.OddCoreCheck
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K5095
public import Certificates.Certificate5118

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.Prop27 in
open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier in
theorem certificate5095 : oddCoreCheck 189 (elemsT L28.QA) (elemsT L28.QP) = true :=
  by simp only [elemsT_eq_elemsV]; exact odd_5095K

end Certificates
