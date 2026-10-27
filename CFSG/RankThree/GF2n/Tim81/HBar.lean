module

public import CFSG.RankThree.GF2n.Tim79aSec2Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {G : Type} [Group G]

@[expose] def kOf (V H : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.centralizer (Tim79a.xOf V H : Set G)

theorem kOf_le (V H : Subgroup G) : kOf V H ≤ H := inf_le_left

theorem mem_kOf_iff {V H : Subgroup G} {x : G} :
    x ∈ kOf V H ↔ x ∈ H ∧ x ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
  Subgroup.mem_inf

theorem le_normalizer_kOf (V H : Subgroup G) : H ≤ Subgroup.normalizer (kOf V H : Set G) :=
  fun h hh => mem_normalizer_inf (Subgroup.le_normalizer (H := H) hh)
    (mem_normalizer_centralizer (Tim79a.H_le_normalizer_xOf V H hh))

instance kOf_normal (V H : Subgroup G) : ((kOf V H).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (kOf_le V H)).2 (le_normalizer_kOf V H)

abbrev HBar (V H : Subgroup G) : Type := ↥H ⧸ (kOf V H).subgroupOf H

@[expose] def piK (V H : Subgroup G) : ↥H →* HBar V H := QuotientGroup.mk' _

@[expose] def imgK (V H S : Subgroup G) : Subgroup (HBar V H) :=
  (S.subgroupOf H).map (piK V H)

theorem piK_surjective (V H : Subgroup G) : Function.Surjective (piK V H) :=
  QuotientGroup.mk'_surjective _

theorem piK_eq_one_iff {V H : Subgroup G} (x : ↥H) :
    piK V H x = 1 ↔ (x : G) ∈ kOf V H :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem mem_imgK_iff {V H S : Subgroup G} {y : HBar V H} :
    y ∈ imgK V H S ↔ ∃ x : ↥H, (x : G) ∈ S ∧ piK V H x = y := by
  simp only [imgK, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem imgK_mono {V H S T : Subgroup G} (hST : S ≤ T) : imgK V H S ≤ imgK V H T :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (hST (Subgroup.mem_subgroupOf.mp hx))

theorem imgK_conjSubgroup {V H S : Subgroup G} {g : G} (hg : g ∈ H) (hS : S ≤ H) :
    imgK V H (conjSubgroup g S) = conjSubgroup (piK V H ⟨g, hg⟩) (imgK V H S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : g⁻¹ * (x : G) * g ∈ S := mem_conjSubgroup.1 hx
    refine mem_conjSubgroup.mpr ?_
    refine (mem_imgK_iff).mpr ⟨⟨g, hg⟩⁻¹ * x * ⟨g, hg⟩, ?_, ?_⟩
    · simpa using hx'
    · simp only [map_mul, map_inv]
  · intro hy
    have hy' : (piK V H ⟨g, hg⟩)⁻¹ * y * piK V H ⟨g, hg⟩ ∈ imgK V H S :=
      mem_conjSubgroup.1 hy
    obtain ⟨z, hz, hzq⟩ := (mem_imgK_iff).mp hy'
    refine (mem_imgK_iff).mpr ⟨⟨g, hg⟩ * z * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · refine mem_conjSubgroup.mpr ?_
      have hcoe : g⁻¹ * ((⟨g, hg⟩ * z * ⟨g, hg⟩⁻¹ : ↥H) : G) * g = (z : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hcoe]
      exact hz
    · rw [show piK V H (⟨g, hg⟩ * z * ⟨g, hg⟩⁻¹) =
          piK V H ⟨g, hg⟩ * piK V H z * (piK V H ⟨g, hg⟩)⁻¹ by simp, hzq]
      group

theorem imgK_sup {V H S T : Subgroup G} (hS : S ≤ H) (hT : T ≤ H) :
    imgK V H S ⊔ imgK V H T = imgK V H (S ⊔ T) := by
  rw [imgK, imgK, imgK, ← Subgroup.map_sup, Subgroup.subgroupOf_sup hS hT]

theorem imgK_self (V H : Subgroup G) : imgK V H H = ⊤ := by
  rw [imgK, Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective (piK V H) (piK_surjective V H)

end CFSG.RankThree.GF2n.Tim81
