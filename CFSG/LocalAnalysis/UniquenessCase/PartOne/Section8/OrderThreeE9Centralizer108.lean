module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69Setup4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

private theorem conj_mem_center_map_of_mem_normalizer {R : Subgroup G} {a z : G}
    (han : a ∈ Subgroup.normalizer (R : Set G))
    (hz : z ∈ (Subgroup.center ↥R).map R.subtype) :
    a * z * a⁻¹ ∈ (Subgroup.center ↥R).map R.subtype := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
  have hazR : a * (c : G) * a⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp han (c : G)).1 c.2
  refine Subgroup.mem_map.mpr ⟨⟨a * (c : G) * a⁻¹, hazR⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro s
  apply Subtype.ext
  have h1 : a⁻¹ * (s : G) * a ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (R : Set G)).inv_mem han) (s : G)).1 s.2
    simpa using h
  have h2 : (a⁻¹ * (s : G) * a) * (c : G) = (c : G) * (a⁻¹ * (s : G) * a) := by
    have h := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hc ⟨a⁻¹ * (s : G) * a, h1⟩)
    simpa using h
  show (s : G) * (a * (c : G) * a⁻¹) = (a * (c : G) * a⁻¹) * (s : G)
  calc (s : G) * (a * (c : G) * a⁻¹)
      = a * ((a⁻¹ * (s : G) * a) * (c : G)) * a⁻¹ := by group
    _ = a * ((c : G) * (a⁻¹ * (s : G) * a)) * a⁻¹ := by rw [h2]
    _ = (a * (c : G) * a⁻¹) * (s : G) := by group

private theorem le_normalizer_center_map (R : Subgroup G) :
    R ≤ Subgroup.normalizer ((Subgroup.center ↥R).map R.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro r hr k hk
  exact conj_mem_center_map_of_mem_normalizer (Subgroup.le_normalizer hr) hk

private theorem le_normalizer_center_map_of_le_normalizer {R A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (R : Set G)) :
    A ≤ Subgroup.normalizer ((Subgroup.center ↥R).map R.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha k hk
  exact conj_mem_center_map_of_mem_normalizer (hAN ha) hk

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
