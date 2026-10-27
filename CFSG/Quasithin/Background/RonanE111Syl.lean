module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.E1Sec7

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_isTwoQuotient {U S N Y : Subgroup G} (hS : IsSylowIn 2 S U) (hNU : N ≤ U)
    (hYN : Y ≤ N) (hNn : ∀ u ∈ U, ∀ x ∈ N, u * x * u⁻¹ ∈ N)
    (hYn : ∀ u ∈ U, ∀ y ∈ Y, u * y * u⁻¹ ∈ Y) (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ Y) :
    N ≤ S ⊔ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYU : Y ≤ U := hYN.trans hNU
  have hUnorm : ∀ {Z : Subgroup G}, Z ≤ U → (∀ u ∈ U, ∀ z ∈ Z, u * z * u⁻¹ ∈ Z) →
      (Z.subgroupOf U).Normal := by
    intro Z hZU hZ
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZU]
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hZ u hu z hz, fun hz => ?_⟩
    have := hZ u⁻¹ (U.inv_mem hu) _ hz
    simpa [mul_assoc] using this
  haveI hYn' : (Y.subgroupOf U).Normal := hUnorm hYU hYn
  haveI hNn' : (N.subgroupOf U).Normal := hUnorm hNU hNn
  set π := QuotientGroup.mk' (Y.subgroupOf U) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hSylS' : IsSylowIn 2 (S.subgroupOf U) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective U.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hS.1, Subgroup.map_top, Subgroup.range_subtype]
    exact hS
  have hSylbar : IsSylowIn 2 ((S.subgroupOf U).map π) ⊤ := E1.isSylowIn_two_map_top hπs hSylS'
  have hNp : IsPGroup 2 ((N.subgroupOf U).map π) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    obtain ⟨k, hk⟩ := h2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨k, Subtype.ext ?_⟩
    show (y : _ ⧸ Y.subgroupOf U) ^ 2 ^ k = 1
    rw [← hxy, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  haveI : ((N.subgroupOf U).map π).Normal := Subgroup.Normal.map hNn' π hπs
  have hle : (N.subgroupOf U).map π ≤ (S.subgroupOf U).map π :=
    hSylbar.le_of_normal le_top (Subgroup.normal_subgroupOf) hNp
  have hle' : N.subgroupOf U ≤ S.subgroupOf U ⊔ Y.subgroupOf U := by
    intro x hx
    have h1 : π x ∈ (S.subgroupOf U).map π := hle ⟨x, hx, rfl⟩
    have h2 : x ∈ ((S.subgroupOf U).map π).comap π := h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have := Subgroup.map_mono (f := U.subtype) hle'
  rwa [Subgroup.map_subgroupOf_eq_of_le hNU, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hS.1, Subgroup.map_subgroupOf_eq_of_le hYU] at this

end CFSG.Quasithin.RonanE111
