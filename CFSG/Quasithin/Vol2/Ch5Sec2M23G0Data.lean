module

public import CFSG.Quasithin.Recognition.M22UniqueData
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.Quasithin.Vol2.Ch5Sec2M23G0DataInputs
public import Certificates.Certificate7056

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Mathieu CFSG.Quasithin.Asc94

theorem m22Bt3_spec :
    (m22Bt3 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Bt3 : Equiv.Perm (Fin 22)) 1 = 1 ∧
    PresHex m22Bt3 ∧ m22Bt3 ^ 3 = 1 ∧ m22Bt3 ≠ 1 :=
  Certificates.certificate7056.1

theorem m22Inv1_spec : (m22Inv1 : Equiv.Perm (Fin 22)) 0 = 0 ∧
    (m22Inv1 : Equiv.Perm (Fin 22)) 1 = 1 ∧ ¬ PresHex m22Inv1 ∧ m22Inv1 * m22Inv1 = 1 ∧
    m22Inv1 * m22Bt3 * m22Inv1 * m22Bt3 = 1 :=
  Certificates.certificate7056.2.1

theorem m22Fix19_inv_spec :
    m22Fix19 * m22Fix19 = 1 ∧ m22Fix19 * m22Bt3 * m22Fix19 * m22Bt3 = 1 :=
  Certificates.certificate7056.2.2

end CFSG.Quasithin.H13
