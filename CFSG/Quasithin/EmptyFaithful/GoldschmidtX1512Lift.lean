module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Fix

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace X1512

variable {G : Type} [Group G] {K C : Subgroup G} {Y : Type*} [Group Y] {ρ : ↥K →* Y}

theorem mem_iff_map_eq_one (hker : ρ.ker = C.subgroupOf K) {g : G} (hg : g ∈ K) :
    g ∈ C ↔ ρ ⟨g, hg⟩ = 1 := by
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

theorem le_of_map_eq_top (hker : ρ.ker = C.subgroupOf K) {P : Subgroup G} (hCP : C ≤ P)
    (htop : (P.subgroupOf K).map ρ = ⊤) : K ≤ P := by
  intro h hh
  have : ρ ⟨h, hh⟩ ∈ (P.subgroupOf K).map ρ := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨p, hp, hph⟩ := this
  have h1 : (⟨h, hh⟩ : ↥K)⁻¹ * p ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hph, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at h1
  have h2 : h⁻¹ * (p : G) ∈ C := h1
  have h3 : h = (p : G) * (h⁻¹ * (p : G))⁻¹ := by group
  rw [h3]
  exact P.mul_mem (Subgroup.mem_subgroupOf.mp hp) (P.inv_mem (hCP h2))

theorem datum_conditions {A : Subgroup G} (hker : ρ.ker = C.subgroupOf K) (hAK : A ≤ K) (xh : ↥K)
    (hx3 : ρ xh ^ 3 = 1)
    (hnorm : ∀ g ∈ (A.subgroupOf K).map ρ,
      g * ρ xh * g⁻¹ = ρ xh ∨ g * ρ xh * g⁻¹ = (ρ xh)⁻¹)
    (hinv : ∃ g ∈ (A.subgroupOf K).map ρ, g * ρ xh * g⁻¹ = (ρ xh)⁻¹) :
    (xh : G) ^ 3 ∈ C ∧
      (∀ a ∈ A, a * (xh : G) * a⁻¹ * (xh : G)⁻¹ ∈ C ∨ a * (xh : G) * a⁻¹ * (xh : G) ∈ C) ∧
      ∃ a ∈ A, a * (xh : G) * a⁻¹ * (xh : G) ∈ C := by
  have hxK := xh.2
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_iff_map_eq_one hker (K.pow_mem hxK 3)]
    have : (⟨(xh : G) ^ 3, K.pow_mem hxK 3⟩ : ↥K) = xh ^ 3 := rfl
    rw [this, map_pow]
    exact hx3
  · intro a ha
    have haK : a ∈ K := hAK ha
    have hga : ρ ⟨a, haK⟩ ∈ (A.subgroupOf K).map ρ :=
      ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rcases hnorm _ hga with h | h
    · left
      rw [mem_iff_map_eq_one hker (K.mul_mem (K.mul_mem (K.mul_mem haK hxK) (K.inv_mem haK))
        (K.inv_mem hxK))]
      have : (⟨a * (xh : G) * a⁻¹ * (xh : G)⁻¹, _⟩ : ↥K) = ⟨a, haK⟩ * xh * ⟨a, haK⟩⁻¹ * xh⁻¹ :=
        rfl
      rw [this]
      simp only [map_mul, map_inv, h]
      group
    · right
      rw [mem_iff_map_eq_one hker (K.mul_mem (K.mul_mem (K.mul_mem haK hxK) (K.inv_mem haK)) hxK)]
      have : (⟨a * (xh : G) * a⁻¹ * (xh : G), _⟩ : ↥K) = ⟨a, haK⟩ * xh * ⟨a, haK⟩⁻¹ * xh := rfl
      rw [this]
      simp only [map_mul, map_inv, h]
      group
  · obtain ⟨g, ⟨a', ha', rfl⟩, hg⟩ := hinv
    have haK : (a' : G) ∈ K := a'.2
    have ha : (a' : G) ∈ A := Subgroup.mem_subgroupOf.mp ha'
    refine ⟨a', ha, ?_⟩
    rw [mem_iff_map_eq_one hker (K.mul_mem (K.mul_mem (K.mul_mem haK hxK) (K.inv_mem haK)) hxK)]
    have : (⟨(a' : G) * (xh : G) * (a' : G)⁻¹ * (xh : G), _⟩ : ↥K) = a' * xh * a'⁻¹ * xh := rfl
    rw [this]
    simp only [map_mul, map_inv]
    rw [hg]
    group

theorem card_eq_inf_mul_card_map {A : Subgroup G} (hker : ρ.ker = C.subgroupOf K) (hAK : A ≤ K) :
    Nat.card A = Nat.card ↥(A ⊓ C) * Nat.card ↥((A.subgroupOf K).map ρ) := by
  let ψ : ↥A →* Y := ρ.comp (Subgroup.inclusion hAK)
  have h := Subgroup.card_ker_mul_card_range ψ
  have hr : ψ.range = (A.subgroupOf K).map ρ := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a, hAK a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hk : ψ.ker = (A ⊓ C).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ a = ρ ⟨a, hAK a.2⟩ := rfl
    rw [h1, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hc : Nat.card ((A ⊓ C).subgroupOf A) = Nat.card ↥(A ⊓ C) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hk, hc, hr] at h
  exact h.symm

end X1512

end CFSG.Quasithin
