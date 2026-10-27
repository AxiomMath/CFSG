module

import all CFSG.Fischer.F4
public import CFSG.Monster.B.Classical.UnitarySixForm

public section

namespace CFSG.Monster.B.Classical.UnitarySix

open CFSG.Fischer

theorem card_isotropic_vec :
    Fintype.card {v : V // v ≠ 0 ∧ herm v v = 0 ∧ True} = 2079 := by
  decide +kernel

theorem card_neighbor_vec :
    Fintype.card {v : V // v ≠ 0 ∧ herm v v = 0 ∧
      (herm (Pi.single 0 1) v = 0 ∧ ∃ i : Fin 6, i ≠ 0 ∧ v i ≠ 0)} = 540 := by
  decide +kernel

theorem card_common_adj_vec :
    Fintype.card {v : V // v ≠ 0 ∧ herm v v = 0 ∧
      (herm (Pi.single 0 1) v = 0 ∧ herm (Pi.single 1 1) v = 0 ∧
        (∃ i : Fin 6, i ≠ 0 ∧ v i ≠ 0) ∧ ∃ i : Fin 6, i ≠ 1 ∧ v i ≠ 0)} = 153 := by
  decide +kernel

theorem card_common_nonadj_vec :
    Fintype.card {v : V // v ≠ 0 ∧ herm v v = 0 ∧
      (herm (Pi.single 0 1) v = 0 ∧ herm (Pi.single 5 1) v = 0)} = 135 := by
  decide +kernel

theorem pair_isotropic : ∀ i j : Fin 6, (i, j) ∈ [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] →
    herm (Pi.single i 1 + Pi.single j 1) (Pi.single i 1 + Pi.single j 1) = 0 ∧
      Pi.single i 1 + Pi.single j 1 ≠ (0 : V) := by
  decide +kernel

end CFSG.Monster.B.Classical.UnitarySix
