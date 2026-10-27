module

public import CFSG.Certificates.Kernel.BabyMonster.SevenGenFact
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.SevenGen
import Certificates.Kernel.BabyMonster.SevenMem
import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Sound

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.BM in
theorem certificate17430 : SevenGen.FactSevenGen ∧
    CFSG.Blueprint.NativeSporadic.decode 2 4370 1 CFSG.Blueprint.NativeSporadic.BSeed1 =
      stripMat Seeds.A1 ∧
    CFSG.Blueprint.NativeSporadic.decode 2 4370 1 CFSG.Blueprint.NativeSporadic.BSeed2 =
      stripMat Seeds.A2 ∧
    ∀ S : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2)), stripMat Seeds.A1 ∈ S →
      stripMat Seeds.A2 ∈ S → stripMat Seven.g ∈ S ∧ stripMat SevenGen.gi ∈ S ∧
        stripMat SevenGen.s2 ∈ S ∧ stripMat SevenGen.s2i ∈ S :=
  ⟨KernelBM.SevenGen.factSevenGen_of, KernelBM.genA₁_eq_stripMat, KernelBM.genA₂_eq_stripMat,
    fun _ hA1 hA2 => CFSG.KC.BM.SevenMem.seven_mem hA1 hA2⟩

end Certificates
