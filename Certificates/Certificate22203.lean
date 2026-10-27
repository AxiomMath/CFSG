
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowCertInputs
import Certificates.Kernel.LocalComp.L34Syl3.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22203 :
    (normT0OK (enumBFS 42 gensS 20160).tabs && centerT0OK &&
      enumOK 42 (wordTabs wU₁) (enumBFS 42 (wordTabs wU₁) 16) &&
      (enumBFS 42 (wordTabs wU₁) 16).tabs.size == 16 &&
      enumOK 42 (wordTabs wU₂) (enumBFS 42 (wordTabs wU₂) 16) &&
      (enumBFS 42 (wordTabs wU₂) 16).tabs.size == 16 &&
      (allBelow 16 fun k => found (indexOf (enumBFS 42 (wordTabs wU₁) 16).tabs)
        (enumBFS 42 (wordTabs wU₁) 16).tabs (tgT k)) &&
      (allBelow 16 fun k => found (indexOf (enumBFS 42 (wordTabs wU₂) 16).tabs)
        (enumBFS 42 (wordTabs wU₂) 16).tabs (tgT (4 * k))) &&
      normalOK 42 (enumBFS 42 (wordTabs wU₁) 16).tabs (wordTabs wP₁)
        ((wordTabs wP₁).map (invTab 42)) (wordTabs wU₁) &&
      normalOK 42 (enumBFS 42 (wordTabs wU₂) 16).tabs (wordTabs wP₂)
        ((wordTabs wP₂).map (invTab 42)) (wordTabs wU₂) &&
      prodOK) = true := KernelLC.L34Syl3.facts22203

end Certificates
