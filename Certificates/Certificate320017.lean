module

public import Certificates.Data.G23RecogHCharInputs
import Certificates.Kernel.HcConj.ClassesGlue

public section

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData
  CFSG.GH74.QTGen4.Recog.G23.HCharData in
theorem certificate320017 : F5Eq ∧ RepLOK ∧ KFstOK ∧ RepOK ∧ InvOK ∧ OrdOK ∧ DOK ∧ ClassOK ∧ CtOK ∧ AOK :=
  CFSG.KC.HcPack.certificate320017_facts

end Certificates
