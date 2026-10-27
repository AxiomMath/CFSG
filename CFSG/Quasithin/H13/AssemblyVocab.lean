module

public import CFSG.Open.QuasithinDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.Quasithin.H13

variable {G : Type*} [Group G]

theorem isSubnormal_open_iff {H K : Subgroup G} :
    CFSG.Open.IsSubnormal H K ↔ CFSG.Assembly.IsSubnormal H K :=
  CFSG.Assembly.isSubnormal_iff_open.symm

theorem quasithinIsCComponent_open_iff {L X : Subgroup G} :
    CFSG.Open.quasithinIsCComponent L X ↔ CFSG.Assembly.Quasithin.quasithinIsCComponent L X := by
  unfold CFSG.Open.quasithinIsCComponent CFSG.Assembly.Quasithin.quasithinIsCComponent
  simp only [isSubnormal_open_iff]

theorem isComponentOf_open_iff {L K : Subgroup G} :
    CFSG.Open.IsComponentOf L K ↔ CFSG.Assembly.IsComponentOf L K :=
  CFSG.Assembly.isComponentOf_iff_open.symm

theorem quasithinGenFitting_open_eq (L : Subgroup G) :
    CFSG.Open.quasithinGenFitting L = CFSG.Assembly.Quasithin.quasithinGenFitting L := by
  unfold CFSG.Open.quasithinGenFitting CFSG.Assembly.Quasithin.quasithinGenFitting
  congr 2
  ext K
  exact isComponentOf_open_iff

theorem quasithinIsLocal_open_iff {T L : Subgroup G} :
    CFSG.Open.quasithinIsLocal T L ↔ CFSG.Assembly.Quasithin.quasithinIsLocal T L := by
  unfold CFSG.Open.quasithinIsLocal CFSG.Assembly.Quasithin.quasithinIsLocal
  rw [quasithinIsCComponent_open_iff]

theorem quasithinIsFaithfulLocal_open_iff {T L : Subgroup G} :
    CFSG.Open.quasithinIsFaithfulLocal T L ↔
      CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal T L := by
  unfold CFSG.Open.quasithinIsFaithfulLocal CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal
  rw [quasithinIsLocal_open_iff, quasithinGenFitting_open_eq]
  rfl

end CFSG.Quasithin.H13
