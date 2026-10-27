module

public import Certificates.Certificate17003

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

@[expose] def AscCox.D
    {m : AscModel z} (c : AscCox m) : Subgroup G := D6.map c.ρ

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem mem_D
    {g : G} : g ∈ c.D ↔ ∃ d ∈ D6, c.ρ d = g := Subgroup.mem_map

theorem card_D : Nat.card c.D = 9 := by
  have e : ↥D6 ≃* ↥c.D := D6.equivMapOfInjective c.ρ c.ρ_inj
  rw [← Nat.card_congr e.toEquiv]
  have : Nat.card ↥D6 = Nat.card {d // d ∈ D6l} := rfl
  rw [this, Nat.card_congr (Equiv.subtypeEquivRight (fun d => (List.mem_toFinset (l := D6l)).symm)),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup D6l_nodup]
  rfl

instance finite_D
    : Finite c.D := Nat.finite_of_card_ne_zero (by rw [card_D]; norm_num)

theorem mem_normalizer_D {g : G} :
    g ∈ Subgroup.normalizer (c.D : Set G) ↔ ∀ d ∈ D6, ∃ d' ∈ D6, g * c.ρ d * g⁻¹ = c.ρ d' := by
  constructor
  · intro hg d hd
    have : g * c.ρ d * g⁻¹ ∈ c.D :=
      (Subgroup.mem_normalizer_iff.1 hg _).1 (Subgroup.mem_map_of_mem _ hd)
    obtain ⟨d', hd', e⟩ := (mem_D c).1 this
    exact ⟨d', hd', e.symm⟩
  · intro h
    have : Finite ↥(c.D : Set G) := (inferInstance : Finite ↥c.D)
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨d, hd, rfl⟩ := (mem_D c).1 hn
    obtain ⟨d', hd', e⟩ := h d hd
    rw [e]
    exact (mem_D c).2 ⟨d', hd', rfl⟩

theorem rho_mem_normalizer (σ : Perm (Fin 6)) :
    c.ρ σ ∈ Subgroup.normalizer (c.D : Set G) ↔ NormDb σ = true := by
  rw [mem_normalizer_D, NormDb_iff]
  refine forall₂_congr fun d hd => ?_
  constructor
  · rintro ⟨d', hd', e⟩
    have : σ * d * σ⁻¹ = d' := by
      apply c.ρ_inj
      rw [map_mul, map_mul, map_inv, e]
    rw [this]
    exact hd'
  · intro h
    exact ⟨σ * d * σ⁻¹, h, by rw [map_mul, map_mul, map_inv]⟩

end AscCox

namespace OuterData

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem rhoy_mem_normalizer
    (h : OuterData c y) (σ : Perm (Fin 6)) :
    c.ρ σ * y ∈ Subgroup.normalizer (c.D : Set G) ↔ NormEb σ = true := by
  rw [AscCox.mem_normalizer_D, NormEb_iff]
  have key : ∀ d : Perm (Fin 6), c.ρ σ * y * c.ρ d * (c.ρ σ * y)⁻¹ =
      c.ρ (σ * outerAlpha d * σ⁻¹) := by
    intro d
    have := h.conj_rho d
    calc c.ρ σ * y * c.ρ d * (c.ρ σ * y)⁻¹ = c.ρ σ * (y * c.ρ d * y⁻¹) * (c.ρ σ)⁻¹ := by group
      _ = c.ρ (σ * outerAlpha d * σ⁻¹) := by
        rw [this, map_mul, map_mul, map_inv]
  refine forall₂_congr fun d hd => ?_
  rw [key]
  constructor
  · rintro ⟨d', hd', e⟩
    rw [c.ρ_inj e]
    exact hd'
  · intro hh
    exact ⟨_, hh, rfl⟩

@[expose] def K
    (h : OuterData c y) : Subgroup G := h.L ⊓ Subgroup.normalizer (c.D : Set G)

theorem K_le_L
    (h : OuterData c y) : h.K ≤ h.L := inf_le_left

theorem K_le_normalizer
    (h : OuterData c y) : h.K ≤ Subgroup.normalizer (c.D : Set G) := inf_le_right

theorem mem_K
    (h : OuterData c y) {g : G} : g ∈ h.K ↔ g ∈ h.L ∧ g ∈ Subgroup.normalizer (c.D : Set G) := Iff.rfl

theorem rho_mem_K
    (h : OuterData c y) (σ : Perm (Fin 6)) :
    c.ρ σ ∈ h.K ↔ Equiv.Perm.sign σ = 1 ∧ NormDb σ = true := by
  rw [mem_K, h.rho_mem_L, AscCox.rho_mem_normalizer]

theorem rhoy_mem_K
    (h : OuterData c y) (σ : Perm (Fin 6)) :
    c.ρ σ * y ∈ h.K ↔ Equiv.Perm.sign σ = 1 ∧ NormEb σ = true := by
  rw [mem_K, h.rhoy_mem_L, h.rhoy_mem_normalizer]

theorem card_normD : Nat.card {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ NormDb σ = true} = 36 :=
  Certificates.certificate17003.1

theorem card_normE : Nat.card {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ NormEb σ = true} = 36 :=
  Certificates.certificate17003.2

theorem K_card
    (h : OuterData c y) : Nat.card h.K = 72 := by
  let f : ({σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ NormDb σ = true} ⊕
      {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ NormEb σ = true}) → ↥h.K :=
    Sum.elim (fun σ => ⟨c.ρ σ.1, (h.rho_mem_K σ.1).2 σ.2⟩)
      (fun σ => ⟨c.ρ σ.1 * y, (h.rhoy_mem_K σ.1).2 σ.2⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (⟨σ, hσ⟩ | ⟨σ, hσ⟩) (⟨τ, hτ⟩ | ⟨τ, hτ⟩) e
      · have := c.ρ_inj (congrArg Subtype.val e)
        subst this
        rfl
      · exact absurd (congrArg Subtype.val e) (h.rho_ne_rhoy σ τ)
      · exact absurd (congrArg Subtype.val e).symm (h.rho_ne_rhoy τ σ)
      · have := c.ρ_inj (mul_right_cancel (congrArg Subtype.val e))
        subst this
        rfl
    · rintro ⟨g, hg⟩
      obtain ⟨hgL, hgN⟩ := hg
      obtain ⟨σ, hσ, rfl | rfl⟩ := hgL
      · refine ⟨Sum.inl ⟨σ, hσ, (c.rho_mem_normalizer σ).1 hgN⟩, rfl⟩
      · refine ⟨Sum.inr ⟨σ, hσ, (h.rhoy_mem_normalizer σ).1 hgN⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum, card_normD, card_normE]

end OuterData

end CFSG.Quasithin
