module

public import CFSG.Sporadic.SuzRecog.LocalR
public import CFSG.Sporadic.SuzRecog.LocalRFusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification.AS81
  CFSG.Sporadic.SuzOddCore

variable {G : Type} [Group G] [Finite G]

theorem exists_suzLocalR_leaf_of_isConj (S : Setting G) (hw : S.width = 3)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (σ : S.M ≃* ↥(invE 1))
    (hL34 : SuzL34Data S.z) {l : ↥(invE 1)} (hl : IsConj lambda4 l) {T : Subgroup ↥(invE 1)}
    (hMF : LocModel l T) : ∃ A R : Subgroup G, SuzLocalR S.z σ l T A R :=
  exists_suzLocalR S σ hL34 (nonCentralSylow S hw hΩ hNWC σ)
    (fun t ht => (not_isConj_iff S hw hΩ hNWC σ t ht).trans
      ⟨fun h => h.trans hl, fun h => h.trans hl.symm⟩) hMF

end CFSG.Sporadic.SuzRecog.LocalR
