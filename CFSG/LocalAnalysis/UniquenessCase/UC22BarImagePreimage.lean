module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barPreimage_barImage_eq_sup_pCore {M H : Subgroup G} (hHM : H ≤ M) :
    barPreimage M (barImage M H) = H ⊔ (CFSG.pCore 2 ↥M).map M.subtype := by
  rw [barPreimage, barImage, Subgroup.comap_map_eq, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hHM, QuotientGroup.ker_mk']

theorem barPreimage_barImage_of_pCoreOf_le {M H : Subgroup G} (hHM : H ≤ M)
    (hN : CFSG.Open.pCoreOf 2 M ≤ H) :
    barPreimage M (barImage M H) = H := by
  rw [barPreimage_barImage_eq_sup_pCore hHM]
  exact sup_eq_left.mpr (by simpa only [CFSG.Open.pCoreOf] using hN)

end CFSG.LocalAnalysis.UniquenessCase.UC22
