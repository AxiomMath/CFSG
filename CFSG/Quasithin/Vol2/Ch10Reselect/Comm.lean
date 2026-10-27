module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_normalizer_fsuVM_of_L (T L I : Subgroup G) :
    L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
  (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)

theorem L_le_normalizer_fsuUL (T L I : Subgroup G) :
    L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
  le_normalizer_commutator (le_normalizer_fsuVM_of_L T L I) (Subgroup.le_normalizer)

theorem fsuUL_le_fsuVM (T L I : Subgroup G) : fsuUL T L I ≤ fsuVM T L I :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_fsuVM_of_L T L I)

theorem conjugate_UL_le_fsuVM (T L I : Subgroup G) {t : G} (ht : t ∈ fsuM T L) :
    CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I := by
  have h := conjugate_mono (fsuUL_le_fsuVM T L I) t
  rwa [conjugate_fsuVM ht] at h

end CFSG.Quasithin.Vol2.Ch10Reselect
