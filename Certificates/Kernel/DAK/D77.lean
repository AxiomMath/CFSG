module

public import Certificates.Data.Kernel.DAK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.DepASmall Certificates.TWDK in
#kc_repo #kc_json_gz CFSG.KD.DAK77 "Certificates/Kernel/DAK/data/d77.json.gz" 4125
  9609975988769878740 (F : List GGDepANPair) (S : List KSingleE)

end
