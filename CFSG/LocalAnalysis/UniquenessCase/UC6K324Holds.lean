module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K324Cls
public import CFSG.LocalAnalysis.UniquenessCase.UC6K324Lie

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

section Two


theorem k324Two_holds : K324Two := by
  intro S _ _ _ idx hr2 hidx he s hso Y hYC hYn hY
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q =>
    rw [TauCeti.LieTypeIndex.characteristic_A] at hr2
    exact false_of_noA6Comp (noA6Comp_linear r q hv (by omega) (by omega) e hso) hYC hYn hY
  | twistedA r q =>
    rw [TauCeti.LieTypeIndex.characteristic_twistedA] at hr2
    exact false_of_noA6Comp (noA6Comp_unitary r q hv (by omega) (by omega) e hso) hYC hYn hY
  | B r q =>
    obtain rfl : r = 2 := hidx
    rw [TauCeti.LieTypeIndex.characteristic_B] at hr2
    exact false_of_noA6Comp (noA6Comp_B2 q hv (by omega) (by omega) e hso) hYC hYn hY
  | G2 q =>
    rw [TauCeti.LieTypeIndex.characteristic_G2] at hr2
    exact false_of_noA6Comp (noA6Comp_G2 q hv (by omega) (by omega) e hso) hYC hYn hY
  | trialityD4 q =>
    rw [TauCeti.LieTypeIndex.characteristic_trialityD4] at hr2
    exact false_of_noA6Comp (noA6Comp_triD4 q hv (by omega) (by omega) e hso) hYC hYn hY
  | reeF4 m => exact false_of_reeF4 m hv e hso hYC hYn hY
  | tits => exact false_of_tits hv e hso hYC hY
  | C _ _ | D _ _ | twistedD _ _ | E6 _ | E7 _ | E8 _ | F4 _ | twistedE6 _ | suzuki _ | reeG2 _ =>
    exact (hidx : False).elim

end Two

section Final


theorem k324_holds
    : K324 :=
  k324_of_two k324Two_holds

end Final

end CFSG.LocalAnalysis.UniquenessCase.UCK
