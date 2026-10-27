module

public import CFSG.Assembly.QuasithinDefs
public import CFSG.Open.QuasithinDefs
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

variable {G : Type*} [Group G]

theorem isSubnormal_assembly_iff_open {H K : Subgroup G} :
    CFSG.Assembly.IsSubnormal H K ↔ CFSG.Open.IsSubnormal H K :=
  CFSG.Assembly.isSubnormal_iff_open

theorem isComponentOf_assembly_iff_open {L K : Subgroup G} :
    CFSG.Assembly.IsComponentOf L K ↔ CFSG.Open.IsComponentOf L K :=
  CFSG.Assembly.isComponentOf_iff_open

theorem quasithinGenFitting_assembly_eq_open (L : Subgroup G) :
    CFSG.Assembly.Quasithin.quasithinGenFitting L = CFSG.Open.quasithinGenFitting L := by
  unfold CFSG.Assembly.Quasithin.quasithinGenFitting CFSG.Open.quasithinGenFitting
  congr 2
  ext K
  exact isComponentOf_assembly_iff_open

theorem quasithinIsCComponent_assembly_iff_open {L X : Subgroup G} :
    CFSG.Assembly.Quasithin.quasithinIsCComponent L X ↔ CFSG.Open.quasithinIsCComponent L X := by
  unfold CFSG.Assembly.Quasithin.quasithinIsCComponent CFSG.Open.quasithinIsCComponent
  simp only [isSubnormal_assembly_iff_open]

theorem quasithinIsLocal_assembly_iff_open {T L : Subgroup G} :
    CFSG.Assembly.Quasithin.quasithinIsLocal T L ↔ CFSG.Open.quasithinIsLocal T L := by
  unfold CFSG.Assembly.Quasithin.quasithinIsLocal CFSG.Open.quasithinIsLocal
  rw [quasithinIsCComponent_assembly_iff_open]

theorem quasithinIsFaithfulLocal_assembly_iff_open {T L : Subgroup G} :
    CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal T L ↔
      CFSG.Open.quasithinIsFaithfulLocal T L := by
  unfold CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal CFSG.Open.quasithinIsFaithfulLocal
  rw [quasithinIsLocal_assembly_iff_open, quasithinGenFitting_assembly_eq_open]
  rfl

end CFSG.Quasithin.EmptyFaithfulMultiple
