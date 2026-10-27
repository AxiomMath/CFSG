module

public import CFSG.Assembly.Defs
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggE8_component_transport {G H : Type} [Group G] [Group H] {C : Subgroup G}
    {C' : Subgroup H} (φ : ↥C ≃* ↥C') {J : Subgroup G} (hJ : IsComponentOf J C) :
    ∃ J' : Subgroup H, IsComponentOf J' C' ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* (↥J' ⧸ Subgroup.center ↥J')) := by
  have hJC : J ≤ C := hJ.1
  have hJcomp : CFSG.IsComponent (J.subgroupOf C) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJC).1 hJ
  let J₁ : Subgroup ↥C' := (J.subgroupOf C).map φ.toMonoidHom
  have hJ₁ : CFSG.IsComponent J₁ :=
    CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent φ hJcomp
  let J' : Subgroup H := J₁.map C'.subtype
  have hJ'le : J' ≤ C' := Subgroup.map_subtype_le J₁
  have hsub : J'.subgroupOf C' = J₁ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := C'.subtype_injective hyx
      simpa [hyx'] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hJ'comp : CFSG.IsComponent (J'.subgroupOf C') := by
    rw [hsub]
    exact hJ₁
  have hJ' : IsComponentOf J' C' :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJ'le).2 hJ'comp
  let e1 : ↥J ≃* ↥(J.subgroupOf C) := (Subgroup.subgroupOfEquivOfLe hJC).symm
  let e2 : ↥(J.subgroupOf C) ≃* ↥J₁ :=
    (J.subgroupOf C).equivMapOfInjective φ.toMonoidHom φ.injective
  let e3 : ↥J₁ ≃* ↥J' := J₁.equivMapOfInjective C'.subtype C'.subtype_injective
  let e : ↥J ≃* ↥J' := e1.trans (e2.trans e3)
  exact ⟨J', hJ', ⟨QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J') e
    (Subgroup.map_center_eq e)⟩⟩

end CFSG.StandardType
