module

public import CFSG.Certificates.Kernel.BabyMonster.SevenFacts
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.SevenElem
import Certificates.Kernel.BabyMonster.SevenElemMem
import Certificates.Kernel.BabyMonster.Seeds

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.BM in
theorem certificate17101 : SevenFacts.Fact17101 ∧
    CFSG.Blueprint.NativeSporadic.decode 2 4370 1 CFSG.Blueprint.NativeSporadic.BSeed1 =
      stripMat Seeds.A1 ∧
    CFSG.Blueprint.NativeSporadic.decode 2 4370 1 CFSG.Blueprint.NativeSporadic.BSeed2 =
      stripMat Seeds.A2 ∧
    ∀ S : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2)), stripMat Seeds.A1 ∈ S →
      stripMat Seeds.A2 ∈ S → stripMat Seven.g ∈ S ∧ stripMat Seven.al ∈ S ∧
        stripMat Seven.t1 ∈ S ∧ stripMat Seven.e3 ∈ S :=
  ⟨KernelBM.SevenFacts.fact17101, KernelBM.genA₁_eq_stripMat, KernelBM.genA₂_eq_stripMat,
    fun _ hA1 hA2 => CFSG.KC.BM.SevenElemMem.seven_elem_mem hA1 hA2⟩

end Certificates
