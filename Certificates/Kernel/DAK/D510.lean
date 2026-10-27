module

public import Certificates.Data.Kernel.DAK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.DepASmall Certificates.TWDK in
#kc_repo #kc_json_gz CFSG.KD.DAK510 "Certificates/Kernel/DAK/data/d510.json.gz" 4462
  3189901456218483300 (F : List GGDepANPair) (S : List KSingleE)

end
