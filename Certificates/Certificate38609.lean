module

public import Certificates.Data.SmithL6Four
public import Certificates.Data.Kernel.SmithL6K
public import Mathlib.Logic.Relation
import Certificates.Kernel.SmithL6K.GlueN

public section

namespace Certificates

open CertificateChecks

theorem certificate38609 :
    CFSG.SmithL6.K.Reach 1953 1953 (fun v => v == 31 || !CFSG.SmithL6.isPartner v)
      (fun g u v => CFSG.SmithL6.tvImg g 0 == 0 && CFSG.SmithL6.tvImg g u == v &&
        (!CFSG.SmithL6.isPartner v || CFSG.SmithL6.isPartner u)) ∧
    ∃ L : List (Nat × Nat × Nat), L.length = 20160 ∧ L.Nodup ∧ ∀ t ∈ L,
      Relation.ReflTransGen
        (fun s t => ∃ g < 1953, CFSG.SmithL6.tvImg g 0 = 0 ∧ CFSG.SmithL6.tvImg g 31 = 31 ∧
          t = CFSG.SmithL6.fourStep g s)
        CFSG.SmithL6.fourBase t :=
  ⟨KernelSmithL6K.reach_partners, KernelSmithL6K.four_orbit⟩

end Certificates
