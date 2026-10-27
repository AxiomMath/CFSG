module

public import Certificates.Certificate10084

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.CosetTable

theorem sp6_card :
    Finite (PG 8 Native.sp6Rels) ∧ Nat.card (PG 8 Native.sp6Rels) ≤ 1451520 :=
  Certificates.certificate10084.1

theorem sp6Cover_card :
    Finite (PG 8 Native.sp6CoverR) ∧ Nat.card (PG 8 Native.sp6CoverR) ≤ 2903040 :=
  Certificates.certificate10084.2

end CFSG.Sporadic.Co2Smith
