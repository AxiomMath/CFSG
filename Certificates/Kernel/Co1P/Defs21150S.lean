module

public import Certificates.Kernel.Co1P.Defs21153

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

@[expose] noncomputable def invK (B o : Nat) (inQ inQ2 : Bool) (d : Nat) : Bool :=
  (fun AB => andB (andB (orderIsK 24 AB o) (memQ B == inQ))
    (andB (memQ (mulWK AB AB) == inQ2) (fixDimIs (unpack24 AB) d))) (mulWK AL B)

@[expose] noncomputable def rep11K (i : Nat) : Nat := if i = 0 then AL else repK (i - 1)

@[expose] noncomputable def invChkK : Bool :=
  (List.range 11).all fun i =>
    invK (rep11K i) (invTable.getD i (0, false, false, 0)).1 (invTable.getD i (0, false, false, 0)).2.1
      (invTable.getD i (0, false, false, 0)).2.2.1 (invTable.getD i (0, false, false, 0)).2.2.2

@[expose] noncomputable def dagInvK : Bool :=
  allN 190 fun j => eqK (mulWK (getL oneK GDS j) (getL oneK GDIS j)) oneK

end CertificateChecks.KernelCo1P

end
