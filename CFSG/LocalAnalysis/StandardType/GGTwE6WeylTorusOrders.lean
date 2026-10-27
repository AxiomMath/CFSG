module

public import Certificates.Certificate1609001
public import CFSG.LieType.SeitzGeneration.ExcTorusUntw
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Matrix

theorem twE6_charpoly_two_spec
    (v : WeylGroup TwistTag.E6.tag)
    (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) :
    (13 ∣ (M.charpoly.eval (2 : ℤ)).natAbs → (M.charpoly.eval (2 : ℤ)).natAbs = 39) ∧
      (19 ∣ (M.charpoly.eval (2 : ℤ)).natAbs → (M.charpoly.eval (2 : ℤ)).natAbs = 57) :=
  Certificates.certificate1609001 v M hv

end CFSG.StandardType.TableCRes

end
