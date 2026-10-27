module

public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.PGroups

open Subgroup

variable {G : Type*} [Group G]

theorem layer_eq_bot_of_isSolvable [Group.IsSolvable G] : layer G = ⊥ :=
  WholeGroup.layer_eq_bot_of_isSolvable

theorem generalizedFitting_eq_fittingSubgroup_of_isSolvable [Group.IsSolvable G] :
    generalizedFitting G = fittingSubgroup G :=
  WholeGroup.generalizedFitting_eq_fittingSubgroup_of_isSolvable

theorem solvable_trivial_complement_core [Finite G] [Group.IsSolvable G] {p : ℕ} (hp : p.Prime)
    (hcore : pPrimeCore p G = ⊥) : IsCharacteristicP p G :=
  have : Fact p.Prime := ⟨hp⟩
  isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot G p hcore layer_eq_bot_of_isSolvable

end CFSG.RankThree.PGroups
