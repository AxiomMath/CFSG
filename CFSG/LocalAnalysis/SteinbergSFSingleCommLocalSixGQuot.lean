module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Order.Minimal

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixG

open Subgroup

section Quot

variable {G : Type} [Group G] {T N : Subgroup G} [(N.subgroupOf T).Normal]

set_option quotPrecheck false in
local notation "π" => QuotientGroup.mk' (N.subgroupOf T)

theorem mem_map_mk_iff {B : Subgroup G} (hNB : N ≤ B) (x : T) :
    π x ∈ (B.subgroupOf T).map π ↔ (x : G) ∈ B := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h1 : y⁻¹ * x ∈ N.subgroupOf T := QuotientGroup.eq.mp hyx
    have h2 := mul_mem (mem_subgroupOf.mp hy) (hNB (mem_subgroupOf.mp h1))
    simpa using h2
  · exact fun hx => mem_map_of_mem _ (mem_subgroupOf.mpr hx)

theorem exists_eq_map (hNT : N ≤ T) (E : Subgroup (↥T ⧸ N.subgroupOf T)) :
    ∃ B : Subgroup G, N ≤ B ∧ B ≤ T ∧ (B.subgroupOf T).map π = E := by
  refine ⟨(E.comap π).map T.subtype, fun x hx => ?_, map_subtype_le _, ?_⟩
  · have h1 : π ⟨x, hNT hx⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hx)
    refine ⟨⟨x, hNT hx⟩, ?_, rfl⟩
    show π ⟨x, hNT hx⟩ ∈ E
    rw [h1]
    exact one_mem _
  · have h1 : ((E.comap π).map T.subtype).subgroupOf T = E.comap π :=
      comap_map_eq_self_of_injective T.subtype_injective _
    rw [h1, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem map_le_map_iff {B B' : Subgroup G} (hNB' : N ≤ B') (hBT : B ≤ T) :
    (B.subgroupOf T).map π ≤ (B'.subgroupOf T).map π ↔ B ≤ B' := by
  constructor
  · intro hle x hx
    exact (mem_map_mk_iff hNB' ⟨x, hBT hx⟩).mp (hle (mem_map_of_mem _ (mem_subgroupOf.mpr hx)))
  · exact fun hle => map_mono fun y hy => mem_subgroupOf.mpr (hle (mem_subgroupOf.mp hy))

theorem isElementaryAbelian_map_iff {B : Subgroup G} (hBT : B ≤ T) :
    IsElementaryAbelian 2 ((B.subgroupOf T).map π) ↔
      ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ N ∧ x * x ∈ N := by
  constructor
  · intro he x hx y hy
    have hx' : π ⟨x, hBT hx⟩ ∈ (B.subgroupOf T).map π := mem_map_of_mem _ (mem_subgroupOf.mpr hx)
    have hy' : π ⟨y, hBT hy⟩ ∈ (B.subgroupOf T).map π := mem_map_of_mem _ (mem_subgroupOf.mpr hy)
    have hc := congrArg Subtype.val (he.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
    have h2 := congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _) (⟨_, hx'⟩ : ((B.subgroupOf T).map π)))
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one] at hc h2
    constructor
    · have h3 : π (⟨x, hBT hx⟩ * ⟨y, hBT hy⟩ * ⟨x, hBT hx⟩⁻¹ * ⟨y, hBT hy⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel]
      exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h3)
    · have h3 : π (⟨x, hBT hx⟩ * ⟨x, hBT hx⟩) = 1 := by rw [map_mul, ← pow_two, h2]
      exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h3)
  · intro hB
    have key : ∀ a ∈ (B.subgroupOf T).map π, ∃ x ∈ B, ∃ hx : x ∈ T, π ⟨x, hx⟩ = a := by
      rintro a ⟨y, hy, rfl⟩
      exact ⟨y, mem_subgroupOf.mp hy, y.2, rfl⟩
    refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x, hx, hxT, hxa⟩ := key a a.2
      obtain ⟨y, hy, hyT, hyb⟩ := key b b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hxa, ← hyb, ← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      have e : ((⟨x, hxT⟩ * ⟨y, hyT⟩ * (⟨y, hyT⟩ * ⟨x, hxT⟩)⁻¹ : T) : G) =
          x * y * x⁻¹ * y⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact (hB x hx y hy).1
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      obtain ⟨x, hx, hxT, hxa⟩ := key a a.2
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hxa, ← map_pow, pow_two, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        mem_subgroupOf]
      exact (hB x hx x hx).2

theorem maximal_map_iff (hNT : N ≤ T) {A B₁ B₂ : Subgroup G} (hAT : A ≤ T) (hN1 : N ≤ B₁)
    (hN2 : N ≤ B₂) (h1A : B₁ ≤ A) (h2A : B₂ ≤ A)
    (he1 : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y * x⁻¹ * y⁻¹ ∈ N ∧ x * x ∈ N)
    (he2 : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y * x⁻¹ * y⁻¹ ∈ N ∧ x * x ∈ N)
    (hcl : ∀ E : Subgroup G, E ≤ A → (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ N ∧ x * x ∈ N) →
      E ≤ B₁ ∨ E ≤ B₂)
    (h12 : ¬ B₁ ≤ B₂) (h21 : ¬ B₂ ≤ B₁) (E : Subgroup (↥T ⧸ N.subgroupOf T)) :
    Maximal (fun S : Subgroup (↥T ⧸ N.subgroupOf T) =>
        S ≤ (A.subgroupOf T).map π ∧ IsElementaryAbelian 2 S) E ↔
      E = (B₁.subgroupOf T).map π ∨ E = (B₂.subgroupOf T).map π := by
  have hP : ∀ {B : Subgroup G}, N ≤ B → B ≤ A →
      (∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ N ∧ x * x ∈ N) →
        (B.subgroupOf T).map π ≤ (A.subgroupOf T).map π ∧
          IsElementaryAbelian 2 ((B.subgroupOf T).map π) := fun hNB hBA he =>
    ⟨(map_le_map_iff (hN1.trans h1A) (hBA.trans hAT)).mpr hBA,
      (isElementaryAbelian_map_iff (hBA.trans hAT)).mpr he⟩
  have hS : ∀ S : Subgroup (↥T ⧸ N.subgroupOf T), S ≤ (A.subgroupOf T).map π →
      IsElementaryAbelian 2 S → S ≤ (B₁.subgroupOf T).map π ∨ S ≤ (B₂.subgroupOf T).map π := by
    intro S hSA hSe
    obtain ⟨B, hNB, hBT, rfl⟩ := exists_eq_map hNT S
    have hBA := (map_le_map_iff (hN1.trans h1A) hBT).mp hSA
    rcases hcl B hBA ((isElementaryAbelian_map_iff hBT).mp hSe) with h | h
    · exact Or.inl ((map_le_map_iff hN1 hBT).mpr h)
    · exact Or.inr ((map_le_map_iff hN2 hBT).mpr h)
  have hne12 : ¬ (B₁.subgroupOf T).map π ≤ (B₂.subgroupOf T).map π := fun h =>
    h12 ((map_le_map_iff hN2 (h1A.trans hAT)).mp h)
  have hne21 : ¬ (B₂.subgroupOf T).map π ≤ (B₁.subgroupOf T).map π := fun h =>
    h21 ((map_le_map_iff hN1 (h2A.trans hAT)).mp h)
  constructor
  · rintro ⟨⟨hEA, hEe⟩, hmax⟩
    rcases hS E hEA hEe with h | h
    · exact Or.inl (le_antisymm h (hmax (hP hN1 h1A he1) h))
    · exact Or.inr (le_antisymm h (hmax (hP hN2 h2A he2) h))
  · rintro (rfl | rfl)
    · refine ⟨hP hN1 h1A he1, fun S hS' hle => ?_⟩
      rcases hS S hS'.1 hS'.2 with h | h
      · exact h
      · exact absurd (hle.trans h) hne12
    · refine ⟨hP hN2 h2A he2, fun S hS' hle => ?_⟩
      rcases hS S hS'.1 hS'.2 with h | h
      · exact absurd (hle.trans h) hne21
      · exact h

end Quot

end SixG

end CFSG.LocalAnalysis.SymplecticFourStandard
