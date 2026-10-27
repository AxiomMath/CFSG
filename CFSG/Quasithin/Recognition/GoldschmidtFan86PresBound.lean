module

public import Certificates.Certificate4220
public import Certificates.Certificate4221
public import Certificates.Certificate4222
public import Certificates.Certificate4223

public section

namespace CFSG.Quasithin.Fan86

open CFSG.CosetTable

theorem card_p1_le :
    Finite (PG 13 p1Words) ∧ Nat.card (PG 13 p1Words) ≤ 5 * 2 ^ 11 :=
  Certificates.certificate4220

theorem card_p1c_le :
    Finite (PG 14 p1cWords) ∧ Nat.card (PG 14 p1cWords) ≤ 5 * 2 ^ 12 :=
  Certificates.certificate4221

theorem card_p2_le :
    Finite (PG 14 p2Words) ∧ Nat.card (PG 14 p2Words) ≤ 3 * 2 ^ 11 :=
  Certificates.certificate4222

theorem card_p2c_le :
    Finite (PG 15 p2cWords) ∧ Nat.card (PG 15 p2cWords) ≤ 3 * 2 ^ 12 :=
  Certificates.certificate4223

end CFSG.Quasithin.Fan86
