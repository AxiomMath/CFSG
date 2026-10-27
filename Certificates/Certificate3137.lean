module

public import Certificates.Kernel.BabyMonster.CTIB.HC5

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelBM.CTIB

open CFSG.Monster.B.GSide CFSG.Monster.B.CTIB.Native CFSG.Monster.B.CTIB in
theorem certificate3137 : (Nat.all (2 ^ 23) (fun m _ => !hc5Comm m || hc5Orbit.contains (hc5Z m)) =
       true)
    ∧ (hc5Wit.length = 64 ∧ hc5Orbit.length = 64 ∧
       (List.range 64).all (fun i => decide (hc5Wit.getD i 0 < 2 ^ 23) &&
         hc5Comm (hc5Wit.getD i 0) && hc5Z (hc5Wit.getD i 0) == hc5Orbit.getD i 0) = true)
    ∧ (hc5Orbit.all (fun z => decide (z < 2 ^ 23) && (z == 0 ||
       (qmul gArr z z == 0 && innerTyRank (innerTy innerTab z) == 2048 &&
         innerTyRank (innerTy innerTab (qmul gArr (2 ^ 22) z)) == 2048 &&
         innerTyRank (innerTy innerTab (qmul gArr 4456968 z)) == 2168 &&
         innerTyRank (innerTy innerTab (qmul gArr 4456968 (qmul gArr (2 ^ 22) z))) == 2168))) =
       true)
    ∧ (hc5Orbit.Nodup) :=
  ⟨HC5.hc5_brute, HC5.hc5_wit, HC5.hc5_rank_codes KernelBM.census_orbitLists, HC5.hc5_nodup⟩

end Certificates
