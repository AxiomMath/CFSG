module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBRho
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBS5

public section

namespace CFSG.Quasithin.H13.GM22

variable {G : Type} [Group G]

namespace PermRho

variable {V : Subgroup G} (ρ : PermRho V)

@[expose] def restr {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    ↥X →* Equiv.Perm (Fin 5) :=
  ρ.φ.comp (Subgroup.inclusion hX)

theorem restr_apply {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) (x : ↥X) :
    ρ.restr hX x = ρ (x : G) := by
  rw [apply_of_mem (hX x.2)]
  rfl

theorem ker_restr {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    (ρ.restr hX).ker = (X ⊓ Subgroup.centralizer (V : Set G)).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, restr_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    eq_one_iff (hX x.2)]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem card_inf_mul_card_range {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) * Nat.card (ρ.restr hX).range =
      Nat.card ↥X := by
  have h1 := Subgroup.card_ker_mul_card_range (ρ.restr hX)
  rw [ker_restr, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  exact h1

include ρ in
theorem exists_cover [Finite G] {T D : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (V : Set G)) (hDT : D ≤ T)
    (hcard : Nat.card D = 4 * Nat.card ↥(D ⊓ Subgroup.centralizer (V : Set G))) :
    ∃ t₀ ∈ T, ∀ t ∈ T,
      (∃ p ∈ D, ∃ q ∈ Subgroup.centralizer (V : Set G), t = p * q) ∨
      ∃ p ∈ D, ∃ q ∈ Subgroup.centralizer (V : Set G), t = t₀ * p * q := by
  have hDN : D ≤ Subgroup.normalizer (V : Set G) := hDT.trans hTN
  have hR2 : IsPGroup 2 (ρ.restr hTN).range := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨k, hk⟩ := hT2 x
    exact ⟨k, Subtype.ext (by simpa [← map_pow] using congrArg (ρ.restr hTN) hk)⟩
  have hRcard : Nat.card (ρ.restr hTN).range ∣ 8 := card_dvd_eight_of_isPGroup _ hR2
  have hKcard : Nat.card (ρ.restr hDN).range = 4 := by
    have h1 := ρ.card_inf_mul_card_range hDN
    have hpos : 0 < Nat.card ↥(D ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
    rw [hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1]; ring)
  have hKR : (ρ.restr hDN).range ≤ (ρ.restr hTN).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, hDT x.2⟩, by rw [restr_apply, restr_apply]⟩
  obtain ⟨r₀, hr₀, hcov⟩ := exists_cover_two _ _ hKR
    (by have := Nat.le_of_dvd (by norm_num) hRcard; omega)
  obtain ⟨⟨t₀, ht₀⟩, rfl⟩ := hr₀
  refine ⟨t₀, ht₀, fun t ht => ?_⟩
  have hρt : ρ t ∈ (ρ.restr hTN).range := ⟨⟨t, ht⟩, restr_apply _ _ _⟩
  rcases hcov (ρ t) hρt with ⟨p, hp⟩ | ⟨p, hp⟩
  · left
    rw [restr_apply] at hp
    exact ⟨p, p.2, (p : G)⁻¹ * t, (ρ.eq_iff (hDN p.2) (hTN ht)).mp hp, by group⟩
  · right
    rw [restr_apply, restr_apply, ← apply_inv (hTN ht₀)] at hp
    have hmul : ρ (t₀ * p) = ρ t := by
      rw [apply_mul (hTN ht₀) (hDN p.2), hp]
      rw [apply_inv (hTN ht₀), mul_inv_cancel_left]
    exact ⟨p, p.2, (t₀ * p)⁻¹ * t,
      (ρ.eq_iff ((Subgroup.mul_mem _ (hTN ht₀) (hDN p.2))) (hTN ht)).mp hmul, by group⟩

end PermRho

end CFSG.Quasithin.H13.GM22
