module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.StandardType

theorem ggNbrLSideQuot_map_equiv {G T : Type} [Group G] [Group T] (π : G →* T)
    (hπ : Function.Injective π) (B : Subgroup G) :
    Nonempty (↥(B.map π) ⧸ Subgroup.center ↥(B.map π) ≃* ↥B ⧸ Subgroup.center ↥B) := by
  let e : ↥B ≃* ↥(B.map π) := Subgroup.equivMapOfInjective B π hπ
  exact ⟨(QuotientGroup.congr (Subgroup.center ↥B) (Subgroup.center ↥(B.map π)) e
    (Subgroup.map_center_eq e)).symm⟩

end CFSG.StandardType
