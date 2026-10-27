module

public import Certificates.Certificate10093

public section

namespace CFSG.YGroups

theorem y000 :
    Finite (YGroup 0 0 0) ∧ Nat.card (YGroup 0 0 0) ≤ 2 :=
  Certificates.certificate10093.1

theorem y100 :
    Finite (YGroup 1 0 0) ∧ Nat.card (YGroup 1 0 0) ≤ 3 * 2 :=
  Certificates.certificate10093.2.1

theorem y110 :
    Finite (YGroup 1 1 0) ∧ Nat.card (YGroup 1 1 0) ≤ 4 * (3 * 2) :=
  Certificates.certificate10093.2.2.1

theorem y111 :
    Finite (YGroup 1 1 1) ∧ Nat.card (YGroup 1 1 1) ≤ 8 * (4 * (3 * 2)) :=
  Certificates.certificate10093.2.2.2.1

theorem y211 :
    Finite (YGroup 2 1 1) ∧ Nat.card (YGroup 2 1 1) ≤ 10 * (8 * (4 * (3 * 2))) :=
  Certificates.certificate10093.2.2.2.2.1

theorem y221 :
    Finite (YGroup 2 2 1) ∧ Nat.card (YGroup 2 2 1) ≤ 51840 :=
  Certificates.certificate10093.2.2.2.2.2.1

theorem y222 :
    Finite (YGroup 2 2 2) ∧ Nat.card (YGroup 2 2 2) ≤ 12597120 :=
  Certificates.certificate10093.2.2.2.2.2.2.1

theorem y322 :
    Finite (YGroup 3 2 2) ∧ Nat.card (YGroup 3 2 2) ≤ 9170703360 :=
  Certificates.certificate10093.2.2.2.2.2.2.2.1

theorem y332 :
    Finite (YGroup 3 3 2) ∧ Nat.card (YGroup 3 3 2) ≤ 258247006617600 :=
  Certificates.certificate10093.2.2.2.2.2.2.2.2.1

theorem y432 :
    Finite (YGroup 4 3 2) ∧ Nat.card (YGroup 4 3 2) ≤ 8178940946586009600 :=
  Certificates.certificate10093.2.2.2.2.2.2.2.2.2

end CFSG.YGroups
