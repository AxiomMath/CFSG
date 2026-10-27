module

public import Certificates.Data.SmithB45ExcHSData
import Certificates.Kernel.HS3850.UTGlue

public section

namespace Certificates

open CFSG.Quasithin.B45Exc.HS CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Bridge.HSExcl in
theorem certificate260391 : hsUTab.check 4 = true ∧ hsUTab.forallGreedyI (fun _ => false) 6 [] = true ∧
    hsUTab.forallGreedyI hsPred4 4 [] = true ∧ hsUTab.forallGreedyI hsPred5 5 [] = true ∧
    hsGenWits.all (genWitOK hsGens hsUTab [hsA0A, hsA1A]) = true ∧
    hsDimWits.all dimWitOK = true :=
  CertificateChecks.KernelHS3850.UT.facts

end Certificates
