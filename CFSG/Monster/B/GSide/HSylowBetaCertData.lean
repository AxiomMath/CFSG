module

public import CFSG.Monster.B.CTIB.HInnerCensus
public import CFSG.Monster.B.CTIB.Rank2158Witness
public meta import CFSG.Monster.B.CTIB.HInnerCert
public import CFSG.Monster.B.GSide.HSylowBetaCertDataInputs
public import Certificates.Certificate3137

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.CTIB
open CFSG.Monster.B.CTIB.Native (qmul gArr autApply liftImgs6)

theorem hc5_brute :
    Nat.all (2 ^ 23) (fun m _ => !hc5Comm m || hc5Orbit.contains (hc5Z m)) =
    true :=
  Certificates.certificate3137.1

theorem hc5_wit : hc5Wit.length = 64 ∧ hc5Orbit.length = 64 ∧
    (List.range 64).all (fun i => decide (hc5Wit.getD i 0 < 2 ^ 23) &&
      hc5Comm (hc5Wit.getD i 0) && hc5Z (hc5Wit.getD i 0) == hc5Orbit.getD i 0) = true :=
  Certificates.certificate3137.2.1

theorem hc5_rank_codes :
    hc5Orbit.all (fun z => decide (z < 2 ^ 23) && (z == 0 ||
    (qmul gArr z z == 0 && innerTyRank (innerTy innerTab z) == 2048 &&
      innerTyRank (innerTy innerTab (qmul gArr (2 ^ 22) z)) == 2048 &&
      innerTyRank (innerTy innerTab (qmul gArr 4456968 z)) == 2168 &&
      innerTyRank (innerTy innerTab (qmul gArr 4456968 (qmul gArr (2 ^ 22) z))) == 2168))) =
    true :=
  Certificates.certificate3137.2.2.1

theorem hc5_nodup : hc5Orbit.Nodup :=
  Certificates.certificate3137.2.2.2

end CFSG.Monster.B.GSide
