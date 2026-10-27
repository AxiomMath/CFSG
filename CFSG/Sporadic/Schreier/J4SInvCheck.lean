
module

public import CFSG.Sporadic.Schreier.J4SInvCheckBase

public import CFSG.Sporadic.Schreier.J4SInvData
public meta import CFSG.Sporadic.Schreier.J4SInvData
public import Certificates.Certificate2172

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

theorem genInv_all : ∀ i < 4, comp11 generatorColumns[i]! genInvColumns[i]! = idRows 11 :=
  Certificates.certificate2172.1

theorem conj_all : ∀ i < 4, ∀ e < 1024, (conjTab[i]!)[e]! < 1024 ∧
    elementColumns[(conjTab[i]!)[e]!]! =
      comp11 (comp11 generatorColumns[i]! elementColumns[e]!) genInvColumns[i]! :=
  Certificates.certificate2172.2.1

theorem forest_all : ∀ j < 19967, (fN j < 2048 ∧ fE j < 1024 ∧ squares[fE j]! = 0 ∧
    app11 elementColumns[fE j]! (fN j) = fN j ∧ ¬ (fN j = 0 ∧ fE j = 0)) ∧
    ((fP j = j ∧ (fE j = 0 ∨ ambIdx (fN j) (fE j) < 77)) ∨
      (fP j < j ∧ fG j < 5 ∧ genMapN (fG j) (fN (fP j)) (fE (fP j)) = fN j ∧
        genMapE (fG j) (fE (fP j)) = fE j)) :=
  Certificates.certificate2172.2.2.1

theorem forest_complete : ∀ e < 1024, ∀ n < 2048,
    (squares[e]! = 0 ∧ app11 elementColumns[e]! n = n ∧ ¬ (n = 0 ∧ e = 0)) →
      (forestIdx[n + 2048 * e]! - 1 < 19967 ∧ fN (forestIdx[n + 2048 * e]! - 1) = n ∧
        fE (forestIdx[n + 2048 * e]! - 1) = e) :=
  Certificates.certificate2172.2.2.2.1

theorem amb_lt : ∀ i < 77, (ambHead[i]!)[0]! < 2048 ∧ (ambHead[i]!)[1]! < 1024 :=
  Certificates.certificate2172.2.2.2.2.1

theorem ambAll_eq : ambAllOK KPairs = true :=
  Certificates.certificate2172.2.2.2.2.2

end CFSG.Sporadic.J4Schreier
