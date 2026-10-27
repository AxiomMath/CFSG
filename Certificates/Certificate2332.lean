module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGHCertElems
import Certificates.Kernel.PresLetters.F2332
import Certificates.Kernel.HSGH.Facts
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.ComponentClassification.HSFLit.GHCert CFSG.KC.MiscCoset

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.HSFLit
  CFSG.ComponentClassification.HSFLit.GHCert CFSG.CosetTable in
theorem certificate2332 : (Finite (PG 9 ghWordsD) ∧ Nat.card (PG 9 ghWordsD) ≤ 512)
    ∧ (∀ r ∈ ghWordsD, FreeGroup.lift (fun i : Fin 9 => ghG i.val) (FreeGroup.mk r) = 1)
    ∧ ∀ k < 512, ∀ k' < 512, nfG k = nfG k' → k = k' :=
  ⟨TableFact.card ghWordsD (by norm_num) CFSG.KBFact.PL2332, KernelHSGH.rels, KernelHSGH.nf_inj⟩

end Certificates
