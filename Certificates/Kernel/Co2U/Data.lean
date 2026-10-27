module

public import Init
public import Certificates.Kernel.Misc.ArrChars
public import Certificates.Data.GF2W1112Co2U
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_arr_chars CertificateChecks.KernelCo2U.W CFSG.GF2W1112.w12UWords

#kc_repo #kc_json_gz CertificateChecks.KernelCo2U.EltP
  "Certificates/Kernel/Co2U/data/elts.json.gz" 4851 17620571204788135205
  (P : List Nat)

end
