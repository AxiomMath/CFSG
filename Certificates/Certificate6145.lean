module

public import Certificates.Data.ONanCMTab
import Certificates.Kernel.ONanCM.Bound
import Certificates.Kernel.ONanCM.Model
public import CFSG.Certificates.CosetTablePresented

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ONanRec.CM CFSG.CosetTable in
theorem certificate6145 : (Finite (PG 6 cmRelWords) ∧ Nat.card (PG 6 cmRelWords) ≤ 161280) ∧
    (cmLettersOK = true ∧ cmRelOK = true ∧ chainOK cmLetters [] cmChain = true ∧
      chainProd cmChain = 161280) :=
  ⟨ONanCM.cmRelWords_card_le, ONanCM.cmModel_facts⟩

end Certificates
