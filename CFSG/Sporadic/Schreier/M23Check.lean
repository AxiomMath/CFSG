
module

public import CFSG.Sporadic.Schreier.M23CheckBase

public import CFSG.Sporadic.Schreier.M23Data
public meta import CFSG.Sporadic.Schreier.M23Data
public import Certificates.Certificate2196
public import Certificates.Certificate2196Base

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Schreier.Native

theorem m23Certificate_check : m23Certificate.check = true :=
  Certificates.certificate2196.1

theorem m23_word_orders :
    ordTest 23 2 (toTable m23PermA) = true ∧ ordTest 23 4 (toTable m23PermB) = true ∧
      pairTest 23 23 6 2 4 (toTable m23PermA) (toTable m23PermB) = true :=
  Certificates.certificate2196.2.1

theorem m23_counts :
    (orderTables m23Certificate 2).length = 3795 ∧
      (orderTables m23Certificate 4).length = 318780 ∧
      classOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (orderTables m23Certificate 2) 4000 = true ∧
      classTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (orderTables m23Certificate 2) (orderTables m23Certificate 4) 4000 23 6 2 4 =
        20401920 :=
  Certificates.certificate2196.2.2

end CFSG.Sporadic.Schreier
