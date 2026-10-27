module

public import Certificates.Data.CFSGNative.ON.Certificate
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.Sporadic.ON.Kernel "Certificates/Data/Kernel/ON/data/basis_x.json.gz" 14827
  4587233633910778088
  (basisXPairs : List (Nat × Nat))

namespace CFSG.Sporadic.ON.Kernel

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native

@[expose] noncomputable def basisXLit : Array W := (basisXPairs.map fun r => ofV ⟨r.1, r.2⟩).toArray

@[expose] def posOrb (x : W) : Nat := (indexOf (orbitData ()).keys).getD x nPts

end CFSG.Sporadic.ON.Kernel

end
