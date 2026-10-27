module

public import CFSG.Monster.B.TwoA.Unitary.TwentyAlgInputs
import Certificates.Kernel.MonsterB.U20.Final

public section

namespace Certificates

open CFSG.Monster.B.TwoA.Unitary in
theorem certificate3082 : (∀ j < 400, wordRows u20Words[j]! = u20RecRows[j]!)
    ∧ (∀ c < 400, CFSG.Monster.B.TwoA.Unitary.combRows unitCert[c]! = eRows c) :=
  ⟨CFSG.KC.U20.records_ok, CFSG.KC.U20.cert_ok⟩

end Certificates
