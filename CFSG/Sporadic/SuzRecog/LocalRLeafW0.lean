module

public import CFSG.Sporadic.SuzRecog.LocalRLeaf
public import CFSG.Sporadic.SuzRecog.C1ModelLoc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification.AS81
  CFSG.Sporadic.SuzOddCore

variable {G : Type} [Group G] [Finite G]

theorem exists_suzLocalR_leaf_w0 (S : Setting G) (hw : S.width = 3)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (σ : S.M ≃* ↥(invE 1))
    (hL34 : SuzL34Data S.z) :
    ∃ A R : Subgroup G,
      SuzLocalR S.z σ C1Model.w0E (C1Model.T0.subgroupOf (invE 1)) A R :=
  exists_suzLocalR_leaf_of_isConj S hw hΩ hNWC σ hL34 C1Model.isConj_lambda4_w0
    C1Model.locModel_w0

end CFSG.Sporadic.SuzRecog.LocalR
