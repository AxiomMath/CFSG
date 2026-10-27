module

public import CFSG.Quasithin.Recognition.ModelBridgesJ3Inputs
import Certificates.Kernel.Misc.RuDigits

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Open CFSG.Blueprint.NativeSporadic in
theorem certificate7033 :
    (nativeModeOneEntries RuSeed1 = quasithinDigits quasithinRuData1)
    ∧ (nativeModeOneEntries RuSeed2 = quasithinDigits quasithinRuData2) := ⟨KernelRu.ch7033_1, KernelRu.ch7033_2⟩

end Certificates
