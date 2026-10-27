module

public import CFSG.Quasithin.H13.NQCatT513L35Defs
import Certificates.Kernel.C7155.Glue
import Certificates.Kernel.C7155.Check

public section

namespace Certificates

open CFSG.Quasithin.H13.NQCat.T513 in
theorem certificate7155 : ∀ g : L35.G35, g ^ 11625 = 1 →
    (∀ t ∈ L35.T0, ∃ a : ℤ, ∃ t' ∈ L35.T0, t * g = g ^ a * t') → g ^ 3 = 1 :=
  CFSG.KC.C7155.c7155_sound CFSG.KD.C7155.ch7155_buckets CFSG.KD.C7155.ch7155_pt
    CFSG.KD.C7155.ch7155_lev

end Certificates
