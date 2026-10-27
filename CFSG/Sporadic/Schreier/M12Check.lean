module

public import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.M12Data
public import Certificates.Certificate2193

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m12Certificate_check : m12Certificate.check = true :=
  Certificates.certificate2193.1

theorem m12_word_orders :
    ordTest 12 2 (toTable m12gA) = true ∧ ordTest 12 3 (toTable m12gB) = true ∧
      pairTest 12 11 6 2 3 (toTable m12gA) (toTable m12gB) = true :=
  Certificates.certificate2193.2.1

theorem m12_order_counts :
    (orderTables m12Certificate 2).length = 891 ∧
      (orderTables m12Certificate 3).length = 4400 :=
  Certificates.certificate2193.2.2.1

theorem m12_pair_count :
    pairCount (orderTables m12Certificate 2) (orderTables m12Certificate 3)
      (pairTest 12 11 6 2 3) = 380160 :=
  Certificates.certificate2193.2.2.2

end CFSG.Sporadic.Schreier
