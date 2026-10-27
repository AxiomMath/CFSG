module

public import CFSG.Quasithin.Recognition.CertTitsPair
import Certificates.Kernel.Tits8074.Count

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin in
theorem certificate8074 : Nat.card (MulAut (Subgroup.closure
    ({titsPermA, titsPermB} : Set (Equiv.Perm (Fin 1755))))) ≤ 2 * 17971200 := by
  rw [← CFSG.Quasithin.titsPairQ_original']
  exact KernelT8074.mulAut_card

end Certificates

end
