module

public import CFSG.Monster.Existence.TwoPoint.Y433MCentralizer
public import CFSG.Monster.Existence.TwoPoint.Y433MB433

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Griess

theorem cent_fiBeta_eq_range_y433M
    (hA : IsTwoACentralizer fiBeta) :
    Subgroup.centralizer ({fiBeta} : Set MGriess) = y433M.range :=
  cent_fiBeta_eq_range_y433M_of_B433 hA finite_B433 isSimpleGroup_B433 natCard_B433_eq

theorem cent_fiBeta_eq_range_y433M_of_all
    (hA : ∀ α, IsConj tGriess α → IsTwoACentralizer α) :
    Subgroup.centralizer ({fiBeta} : Set MGriess) = y433M.range :=
  cent_fiBeta_eq_range_y433M (hA fiBeta isConj_fiBeta)

end CFSG.Monster.Existence
