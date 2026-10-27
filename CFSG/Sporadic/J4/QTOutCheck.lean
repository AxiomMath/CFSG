module

public import CFSG.Sporadic.J4.QTOutNative
public meta import CFSG.Sporadic.J4.QTOutNative
public import CFSG.Sporadic.J4.QTRankCheck
public import Certificates.Certificate4019

public section

namespace CFSG.Sporadic.J4.QT

theorem ucs_lt : ∀ L ∈ ucsMasks, ∀ c ∈ L, c < 2 ^ 11 :=
  Certificates.certificate4019.1

theorem ucs_zero : ucsMasks.getD 0 [] = [0] :=
  Certificates.certificate4019.2.1

theorem ucs_length : ucsMasks.length = 5 :=
  Certificates.certificate4019.2.2.1

theorem ucs_steps :
    ∀ k < 4, ucsStep (ucsMasks.getD k []) (ucsMasks.getD (k + 1) []) = true :=
  Certificates.certificate4019.2.2.2.1

theorem fixesZ4_cases :
    ∀ t ∈ tabL, fixesZ4 t = true → t = idT ∨ t = tET :=
  Certificates.certificate4019.2.2.2.2.1

theorem tET_inv : tET ∈ tabL ∧ compT tET tET = idT ∧ tET ≠ idT :=
  Certificates.certificate4019.2.2.2.2.2.1

theorem tET_fixes : fixesZ4 tET = true :=
  Certificates.certificate4019.2.2.2.2.2.2.1

theorem eT_lt : eT < 1024 :=
  Certificates.certificate4019.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT
