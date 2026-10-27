module

public import CFSG.Quasithin.Recognition.ModelBridgesJ3Inputs
import Certificates.Kernel.Misc.Perm.J3Seeds

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Open CFSG.Blueprint.NativeSporadic in
theorem certificate8085 : (nativeModeOneEntries J3Seed1 = quasithinDigits quasithinJ3Data1)
    ∧ (nativeModeOneEntries J3Seed2 = quasithinDigits quasithinJ3Data2) :=
  ⟨KernelMisc.j3_entries₁, KernelMisc.j3_entries₂⟩

end Certificates
