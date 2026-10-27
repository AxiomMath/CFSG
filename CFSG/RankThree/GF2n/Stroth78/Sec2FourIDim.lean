module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a Module
open CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem conj_mem_centerIn_QaOf (S : Setting z E F) {a c x : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G))
    (hx : x ∈ centerIn (QaOf a)) :
    c * x * c⁻¹ ∈ centerIn (QaOf a) := by
  obtain ⟨hxQa, hxCent⟩ := Subgroup.mem_inf.mp hx
  have hcQa : ∀ y ∈ QaOf a, c * y * c⁻¹ ∈ QaOf a := fun y hy =>
    fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hc hy
  have hcQa_inv : ∀ y ∈ QaOf a, c⁻¹ * y * c ∈ QaOf a := by
    intro y hy
    have h := fStar_normal (M := Subgroup.centralizer ({a} : Set G))
      ((Subgroup.centralizer ({a} : Set G)).inv_mem hc) hy
    simpa [QaOf, Qa] using h
  refine Subgroup.mem_inf.mpr ⟨hcQa x hxQa, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcyc : c⁻¹ * y * c ∈ QaOf a := hcQa_inv y hy
  have hxc : (c⁻¹ * y * c) * x = x * (c⁻¹ * y * c) :=
    Subgroup.mem_centralizer_iff.mp hxCent (c⁻¹ * y * c) hcyc
  calc
    y * (c * x * c⁻¹) = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by group
    _ = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by rw [hxc]
    _ = (c * x * c⁻¹) * y := by group

end CFSG.RankThree.GF2n.Stroth78
