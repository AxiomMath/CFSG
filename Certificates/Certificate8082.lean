module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Quasithin.Recognition.CertU33WreathInputs
import Certificates.Kernel.PresLetters.F8082
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG CFSG.Quasithin CFSG.CosetTable

namespace Certificates

open CFSG CFSG.Quasithin CFSG.CosetTable CFSG.Sporadic.Bridge CFSG.Open in
theorem certificate8082 : Finite (PG 3 u33CRels) ∧ Nat.card (PG 3 u33CRels) ≤ 32 :=
  CFSG.KC.MiscCoset.TableFact.card u33CRels (by norm_num) CFSG.KBFact.F8082

end Certificates
