module

public import CFSG.RankThree.Asc83Table.HSData
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KMcertQSound
import Certificates.Kernel.SectionRankHS.FactsQ

public section

open CFSG CFSG.RankThree CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.HS
  CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CertificateChecks.KernelSRHS

namespace Certificates

open CFSG CFSG.RankThree CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.HS
  CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint in
theorem certificate8000 :
    mcertCheck (ops2fr 20) NativeSporadic.HSSeed1 NativeSporadic.HSSeed2 hsCert = true :=
  CFSG.KC.OpsF2K.mcertCheck_fr_of_K SA.bind SB.bind SA.eq SB.eq
    (CFSG.KC.OpsF2K.mcertK_of_Q mcert_Q)

end Certificates
