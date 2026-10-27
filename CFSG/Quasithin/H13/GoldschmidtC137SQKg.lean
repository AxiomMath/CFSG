module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
import CFSG.Foundations.KCoreClosure
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.Blueprint CFSG.SectionRank

theorem catalog_of_comm {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcomm : ∀ a b : S, a * b = b * a) : Catalog S :=
  CFSG.SectionRank.catalog_containsAbelianSimple S hcomm

theorem isKGroupCat_of_solvable {X : Type} [Group X] [Finite X] (hX : Group.IsSolvable X) :
    IsKGroupCat X :=
  CFSG.KCore.KGroupAllSimple.of_isSolvable CFSG.SectionRank.catalog_containsAbelianSimple hX

theorem isKGroupCat_of_pGroup {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hX : IsPGroup p X) : IsKGroupCat X :=
  haveI := hX.isNilpotent
  isKGroupCat_of_solvable inferInstance

theorem isKGroupCat_of_ker {X Q : Type} [Group X] [Group Q] (f : X →* Q)
    (hk : IsKGroupCat f.ker) (hq : IsKGroupCat Q) : IsKGroupCat X :=
  CFSG.KCore.KGroupAllSimple.of_ker CFSG.SectionRank.catalog_isoInvariant f hk hq

end CFSG.Quasithin.H13.U3.GC137.SQ
