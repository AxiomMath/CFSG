module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Generation
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem mem_of_conj_mem_of_commute_conj {G : Type*} [Group G] {Y : Subgroup G} {b t : G}
    (hbC : Subgroup.centralizer ({b} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G) →
      ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹)
    (hcomm : ∀ g : G, g * t * g⁻¹ ∈ Y → ∃ y ∈ Y, Commute (g * t * g⁻¹) (y * b * y⁻¹))
    {g : G} (hg : g * t * g⁻¹ ∈ Y) : g ∈ Y := by
  obtain ⟨y, hy, hc⟩ := hcomm g hg
  have hh : (g⁻¹ * y) * b * (g⁻¹ * y)⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    calc t * ((g⁻¹ * y) * b * (g⁻¹ * y)⁻¹)
        = g⁻¹ * ((g * t * g⁻¹) * (y * b * y⁻¹)) * g := by group
      _ = g⁻¹ * ((y * b * y⁻¹) * (g * t * g⁻¹)) * g := by rw [hc.eq]
      _ = ((g⁻¹ * y) * b * (g⁻¹ * y)⁻¹) * t := by group
  obtain ⟨y', hy', he⟩ := hfus _ hh
  have hc' : y'⁻¹ * (g⁻¹ * y) ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y'⁻¹ * (g⁻¹ * y) * b = y'⁻¹ * ((g⁻¹ * y) * b * (g⁻¹ * y)⁻¹) * (g⁻¹ * y) := by group
      _ = y'⁻¹ * (y' * b * y'⁻¹) * (g⁻¹ * y) := by rw [he]
      _ = b * (y'⁻¹ * (g⁻¹ * y)) := by group
  have hmem : g⁻¹ * y ∈ Y := by
    have h := Y.mul_mem hy' (hbC hc')
    rwa [mul_inv_cancel_left] at h
  have hgy : g = y * (g⁻¹ * y)⁻¹ := by group
  rw [hgy]
  exact Y.mul_mem hy (Y.inv_mem hmem)

theorem isSylow2In_map_subtype {G : Type} [Group G] {Y : Subgroup G} (U : Sylow 2 ↥Y) :
    IsSylow2In ((U : Subgroup ↥Y).map Y.subtype) Y := by
  refine ⟨Subgroup.map_subtype_le _, U.isPGroup'.map _, fun T hTY hT hUT => ?_⟩
  have hT' : IsPGroup 2 ↥(T.subgroupOf Y) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  have hle : (U : Subgroup ↥Y) ≤ T.subgroupOf Y := Subgroup.map_le_iff_le_comap.mp hUT
  rw [← U.is_maximal' hT' hle, Subgroup.subgroupOf_map_subtype, inf_of_le_left hTY]

end CFSG.StandardType.FrameRoute.FS81
