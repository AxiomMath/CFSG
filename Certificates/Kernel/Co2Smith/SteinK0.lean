module

public import Certificates.Kernel.Co2Smith.SteinDefs
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native

#kc_each stBlkK 0 54

theorem stOpp_k : stOppK = true := by decide +kernel

theorem elt_k : (((List.range 18).all fun r => (List.range 4).all fun c =>
    (decF (eltK r c)).toList.map (·.code.val) == (stElt r c).toList.map (·.code.val)) &&
    (decF oneF).toList.map (·.code.val) == m6One.toList.map (·.code.val)) = true := by
  decide +kernel

@[expose] noncomputable def badGens : List (Nat × Nat) → List (Nat × Nat)
  | a :: b :: l => a :: (b.1, CFSG.KC.Co2InvS.IDP) :: l
  | l => l

theorem stBlk_neg : (!stCheckK (badGens (gensK (stBlock 0 1)))) = true := by decide +kernel

end CertificateChecks.KernelCo2Smith
