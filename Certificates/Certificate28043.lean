module

public import Certificates.Kernel.EvenBN.Thm49ETOData
import Certificates.Kernel.EvenBN.Thm49ETOGen
import Certificates.Kernel.EvenBN.Thm49ETOTabs
import Certificates.Kernel.EvenBN.Thm49ETOSteps
import Certificates.Kernel.EvenBN.Thm49ETOCodes
import Certificates.Kernel.EvenBN.Thm49ETOS0
import Certificates.Kernel.EvenBN.Thm49ETOS1
import Certificates.Kernel.EvenBN.Thm49ETOS2
import Certificates.Kernel.EvenBN.Thm49ETOS3

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49 CertificateChecks.KernelT49

theorem search43 : ∀ i3 < 92, searchK w43 i3 = true := by
  intro i3 hi3
  by_cases h0 : i3 < 23
  · have := allBlk_spec search43_0 i3 h0
    rwa [Nat.add_eq, Nat.zero_add] at this
  by_cases h1 : i3 < 46
  · have := allBlk_spec search43_1 (i3 - 23) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_of_le (by omega)] at this
  by_cases h2 : i3 < 69
  · have := allBlk_spec search43_2 (i3 - 46) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_of_le (by omega)] at this
  · have := allBlk_spec search43_3 (i3 - 69) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_of_le (by omega)] at this

theorem certificate28043 : ∃ W : CFSG.KD.T49.TOW, ∃ P : CFSG.KD.T49.MPerms, ∃ Q : CFSG.KD.T49.KPerms,
    CFSG.KD.T49.TOOK W P Q :=
  ⟨w43, p43, q43, fun _ hj => KernelSpor.Tits2264.gen_eq hj,
    fun _ hj => KernelMisc.TitsText.titsDerivedArrs_get (by omega),
    KernelSporSch.TitsCommon.z_eq, gen43, tab43, steps43, codes43, search43⟩

end Certificates
