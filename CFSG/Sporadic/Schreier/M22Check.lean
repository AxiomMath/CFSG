module

public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import Certificates.Certificate2195

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m22Certificate_check : m22Certificate.check = true :=
  Certificates.certificate2195.1

theorem m22_word_orders :
    ordTest 22 2 (toTable m22gA) = true ∧ ordTest 22 4 (toTable m22gB) = true ∧
      pairTest 22 11 6 2 4 (toTable m22gA) (toTable m22gB) = true :=
  Certificates.certificate2195.2.1

theorem m22_order_counts :
    (orderTables m22Certificate 2).length = 1155 ∧
      (orderTables m22Certificate 4).length = 41580 :=
  Certificates.certificate2195.2.2.1

theorem m22_pair_count :
    pairCount (orderTables m22Certificate 2) (orderTables m22Certificate 4)
      (pairTest 22 11 6 2 4) = 1774080 :=
  Certificates.certificate2195.2.2.2

end CFSG.Sporadic.Schreier
