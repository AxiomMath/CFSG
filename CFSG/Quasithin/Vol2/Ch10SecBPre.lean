module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin

variable {G : Type} [Group G] {X : Subgroup G} {Q : Type*} [Group Q]

@[expose] def preIn (Ψ : ↥X →* Q) (B : Subgroup Q) : Subgroup G := (B.comap Ψ).map X.subtype

@[expose] def imgIn (Ψ : ↥X →* Q) (Y : Subgroup G) : Subgroup Q := (Y.subgroupOf X).map Ψ

theorem mem_preIn {Ψ : ↥X →* Q} {B : Subgroup Q} {x : G} :
    x ∈ preIn Ψ B ↔ ∃ hx : x ∈ X, Ψ ⟨x, hx⟩ ∈ B := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem preIn_le (Ψ : ↥X →* Q) (B : Subgroup Q) : preIn Ψ B ≤ X :=
  fun _ hx => (mem_preIn.mp hx).1

theorem mem_imgIn {Ψ : ↥X →* Q} {Y : Subgroup G} {q : Q} :
    q ∈ imgIn Ψ Y ↔ ∃ (x : G) (hx : x ∈ X), x ∈ Y ∧ Ψ ⟨x, hx⟩ = q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, y.2, hy, rfl⟩
  · rintro ⟨x, hx, hxY, rfl⟩
    exact ⟨⟨x, hx⟩, hxY, rfl⟩

theorem imgIn_mono (Ψ : ↥X →* Q) {Y₁ Y₂ : Subgroup G} (h : Y₁ ≤ Y₂) :
    imgIn Ψ Y₁ ≤ imgIn Ψ Y₂ :=
  Subgroup.map_mono (fun _ hy => h hy)

theorem preIn_mono (Ψ : ↥X →* Q) {B₁ B₂ : Subgroup Q} (h : B₁ ≤ B₂) :
    preIn Ψ B₁ ≤ preIn Ψ B₂ :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem preIn_imgIn {Ψ : ↥X →* Q} {Y : Subgroup G} (hYX : Y ≤ X)
    (hker : ∀ x : ↥X, Ψ x = 1 → (x : G) ∈ Y) : preIn Ψ (imgIn Ψ Y) = Y := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxX, hq⟩ := mem_preIn.mp hx
    obtain ⟨y, hyX, hyY, hy⟩ := mem_imgIn.mp hq
    have h1 : Ψ (⟨y, hyX⟩⁻¹ * ⟨x, hxX⟩) = 1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
    have h2 := Y.mul_mem hyY (hker _ h1)
    simpa using h2
  · intro y hy
    exact mem_preIn.mpr ⟨hYX hy, mem_imgIn.mpr ⟨y, hYX hy, hy, rfl⟩⟩

theorem imgIn_preIn {Ψ : ↥X →* Q} (hΨ : Function.Surjective Ψ) (B : Subgroup Q) :
    imgIn Ψ (preIn Ψ B) = B := by
  ext q
  rw [mem_imgIn]
  constructor
  · rintro ⟨x, hx, hxB, rfl⟩
    obtain ⟨hx', h⟩ := mem_preIn.mp hxB
    exact h
  · intro hq
    obtain ⟨y, rfl⟩ := hΨ q
    exact ⟨y, y.2, mem_preIn.mpr ⟨y.2, hq⟩, rfl⟩

theorem imgIn_oTwoUpper [Finite G] (Ψ : ↥X →* Q) {Y : Subgroup G} (hYX : Y ≤ X) :
    imgIn Ψ (oTwoUpper Y) = oTwoUpper (imgIn Ψ Y) := by
  have hY : (Y.subgroupOf X).map X.subtype = Y := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYX]
  have h1 : (oTwoUpper Y).subgroupOf X = oTwoUpper (Y.subgroupOf X) := by
    conv_lhs => rw [← hY, oTwoUpper_map]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [imgIn, h1, imgIn, oTwoUpper_map]

end CFSG.Quasithin.Vol2.Ch10.SecB
