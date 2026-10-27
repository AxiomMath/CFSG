module

public import CFSG.LieType.Chevalley.WeylRoots
import Certificates.Kernel.TwE6Det.Assembly

public section

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
open scoped Matrix in
theorem certificate1609001 : ∀ (v : WeylGroup TwistTag.E6.tag)
    (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ),
    (∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) →
    (13 ∣ (M.charpoly.eval (2 : ℤ)).natAbs → (M.charpoly.eval (2 : ℤ)).natAbs = 39) ∧
      (19 ∣ (M.charpoly.eval (2 : ℤ)).natAbs → (M.charpoly.eval (2 : ℤ)).natAbs = 57) :=
  CertificateChecks.KernelTwE6Det.charpoly_two

end Certificates
