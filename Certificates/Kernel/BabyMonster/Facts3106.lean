module

public import Certificates.Kernel.BabyMonster.Conj

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.Monster.B.Dyadic CFSG.KC.BM.Ln

theorem fact3106_of : Fact3106 := fun g i t => by
  obtain ⟨Z, hZ, -⟩ := cnumRep g
  rw [hZ, Matrix.map_apply, eq_intCast]
  exact Rat.den_intCast _

end CertificateChecks.KernelBM.Dy

end
