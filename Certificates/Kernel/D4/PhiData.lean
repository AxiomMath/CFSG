module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.TriD4TwoRow
public import CFSG.Open.LocalVocabulary
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

namespace CertificateChecks.KernelD4

meta def lcPH : List Nat := [CFSG.KS.RawGen.pack 12 (CFSG.StandardType.TriD4TwoRow.phiArr ())]

end CertificateChecks.KernelD4

end

#kc_items CertificateChecks.KernelD4.PH include_bytes "data/PhiData.PH.items" 3690 6872797711375889173
