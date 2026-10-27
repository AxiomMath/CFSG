module

public import Certificates.Data.Kernel.BabyMonster.B9201Facts
import Certificates.Kernel.BabyMonster.B9201Prov
import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.Kernel.BabyMonster.SoundDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.BM

open CFSG.Blueprint.NativeSporadic in
theorem certificate9201_of
    (h1 : CFSG.Blueprint.NativeSporadic.decode 2 4370 1 CFSG.Blueprint.NativeSporadic.BSeed1 =
      stripMat Seeds.A1)
    (h2 : CFSG.Blueprint.NativeSporadic.decode 2 4370 1 CFSG.Blueprint.NativeSporadic.BSeed2 =
      stripMat Seeds.A2) :
 CFSG.KC.BM.B9201.B9201Facts (decode 2 4370 1 BSeed1) (decode 2 4370 1 BSeed2) := by
  have h := KernelBM.Run9201.b9201Facts_strip
  rw [← h1, ← h2] at h
  exact h

open CFSG.Blueprint.NativeSporadic in
theorem certificate9201 : CFSG.KC.BM.B9201.B9201Facts (decode 2 4370 1 BSeed1) (decode 2 4370 1 BSeed2) :=
  certificate9201_of KernelBM.genA₁_eq_stripMat KernelBM.genA₂_eq_stripMat

end Certificates

end
