module

public import CFSG.Quasithin.Recognition.CertU33PermInputs
import Certificates.Kernel.Misc.Perm.U33Chain

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native in
theorem certificate8080 : u33Gens.size = 5 ∧ CFSG.YGroups.ModelNative.permsOK 28 u33Gens = true ∧
    u33Gens.size ≤ u33Strong.size ∧ (∀ i < u33Gens.size, u33Strong[i]! = u33Gens[i]!) ∧
    rawChainOK 28 (u33Strong.extract 0 u33Gens.size) u33Strong (u33Base.map Fin.val).toArray
      u33RawWords 1 = true ∧
    rawOrbitSizes 28 u33Strong (u33Base.map Fin.val).toArray = [28, 27, 2, 4] := KernelMisc.U33C.facts

end Certificates
