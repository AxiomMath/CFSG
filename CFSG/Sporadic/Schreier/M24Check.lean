
module

public import CFSG.Sporadic.Schreier.M24CheckBase

public import CFSG.Sporadic.Schreier.M24Data
public meta import CFSG.Sporadic.Schreier.M24Data
public import Certificates.Certificate2198

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m24Certificate_check : m24Certificate.check = true :=
  Certificates.certificate2198.1

theorem m24_word_orders :
    ordTest 24 2 (toTable m24gA) = true ∧ ordTest 24 3 (toTable m24gB) = true ∧
      pairTest 24 23 12 2 3 (toTable m24gA) (toTable m24gB) = true :=
  Certificates.certificate2198.2.1

theorem m24_counts :
    (orderTables m24Certificate 2).length = 43263 ∧
      (orderTables m24Certificate 3).length = 712448 ∧
      classOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (orderTables m24Certificate 2) 40000 = true ∧
      classTotal 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (orderTables m24Certificate 2) (orderTables m24Certificate 3) 40000 23 12 2 3 =
        979292160 :=
  Certificates.certificate2198.2.2

end CFSG.Sporadic.Schreier
