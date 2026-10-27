module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDLocMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoF48Cert

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

set_option linter.unusedSectionVars false


theorem f431_clause1 :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H₁ H₂ : Subgroup G) (z : G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
        (fun Y _ => Nonempty (Y ≃* quasithinTits)) →
      (Nonempty (oTwoQuot ↥H₁ ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H₁ ≃* ↥(Sz 0))) →
      z ∈ H₁ → z ≠ 1 → z ^ 2 = 1 →
      H₁ ≤ Subgroup.centralizer ({z} : Set G) → Subgroup.centralizer ({z} : Set G) ≤ H₁ →
      Nonempty (G ≃* quasithinTits) :=
  fun G _ _ _ => f431_clause1_of_inputs
    (fun Y _ _ β hβ hle => TitsGeo.hF424 Y β hβ hle) titsLocalCent G

end CFSG.Quasithin.H13.F431.TitsD
