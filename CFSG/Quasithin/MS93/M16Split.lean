module

public import CFSG.Quasithin.MS93.M16Spr

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

omit [Field F] in
theorem card_fin3_fun [Finite F] : Nat.card (Multiplicative (Fin 3 → F)) = Nat.card F ^ 3 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3),
    Fintype.card_fin]

theorem injective_of_natural_quotient [CharP F 2] [Finite F] [Finite V]
    {ρ : SL3 F →* MulAut V} {C : Subgroup V}
    (hC : commV ρ.range = C) (hCZ : C ⊔ fixV ρ.range = ⊤)
    (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) C) ≤ Nat.card F)
    (φ : ↥C →* Multiplicative (Fin 3 → F)) (hφs : Function.Surjective φ)
    (hφ : ∀ (g : SL3 F) (v w : ↥C), (w : V) = ρ g v →
      Multiplicative.toAdd (φ w) =
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (φ v)) :
    Function.Injective φ := by
  have hCmem : ∀ (g : SL3 F) (v : V), ρ g v * v⁻¹ ∈ C := fun g v => by
    rw [← hC]; exact comm_mem_commV ρ g v
  have hCinv : ∀ (g : SL3 F), ∀ v ∈ C, ρ g v ∈ C := fun g v hv => by
    rw [← hC] at hv ⊢; exact rho_mem_commV ρ g hv
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) C with hRdef
  have h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ C, ρ g v ∈ C := fun g _ v hv =>
    hCinv g v hv
  have hRC : R ≤ C := by
    rw [hRdef, G6.commOn_le_iff]
    rintro _ ⟨x, -, rfl⟩ v -
    exact hCmem x v
  have hW2 : ∀ r ∈ R, ρ cyc r ∈ C := fun r hr => hCinv cyc r (hRC hr)
  have hN : R ≠ R.map (ρ p01).toMonoidHom := by
    intro hD
    obtain ⟨c₂, hc₂⟩ := hφs (Multiplicative.ofAdd ![0, 0, 1])
    set r : ↥C := ⟨ρ (rootElt 0 2 1) c₂ * (c₂ : V)⁻¹, hCmem _ _⟩ with hr
    have hrR : (r : V) ∈ R :=
      G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨_, rootElt_mem_rootGroup 0 2 1, rfl⟩) c₂.2
    have hφr : Multiplicative.toAdd (φ r) = ![1, 0, 0] := by
      have h1 : r = ⟨ρ (rootElt 0 2 1) c₂, hCinv _ _ c₂.2⟩ * c₂⁻¹ := rfl
      rw [h1, map_mul, map_inv, toAdd_mul, toAdd_inv,
        hφ _ c₂ ⟨ρ (rootElt 0 2 1) c₂, hCinv _ _ c₂.2⟩ rfl, hc₂, toAdd_ofAdd,
        rootElt02_mulVec]
      funext k
      fin_cases k <;> simp
    let L : Subgroup V :=
      { carrier := {v | ∃ h : v ∈ C, Multiplicative.toAdd (φ ⟨v, h⟩) 0 = 0}
        mul_mem' := fun {a b} ⟨ha, ha0⟩ ⟨hb, hb0⟩ => ⟨C.mul_mem ha hb, by
          have : (⟨a * b, C.mul_mem ha hb⟩ : ↥C) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
          rw [this, map_mul, toAdd_mul, Pi.add_apply, ha0, hb0, add_zero]⟩
        one_mem' := ⟨C.one_mem, by
          have : (⟨1, C.one_mem⟩ : ↥C) = 1 := rfl
          rw [this, map_one, toAdd_one, Pi.zero_apply]⟩
        inv_mem' := fun {a} ⟨ha, ha0⟩ => ⟨C.inv_mem ha, by
          have : (⟨a⁻¹, C.inv_mem ha⟩ : ↥C) = (⟨a, ha⟩ : ↥C)⁻¹ := rfl
          rw [this, map_inv, toAdd_inv, Pi.neg_apply, ha0, neg_zero]⟩ }
    have hL : R.map (ρ p01).toMonoidHom ≤ L := by
      rw [map_commOn02_p01 h𝒲, G6.commOn_le_iff]
      rintro _ ⟨x, ⟨s, rfl⟩, rfl⟩ v hv
      refine ⟨hCmem _ v, ?_⟩
      have h1 : (⟨ρ (rootElt 1 2 s) v * v⁻¹, hCmem _ v⟩ : ↥C) =
          ⟨ρ (rootElt 1 2 s) v, hCinv _ v hv⟩ * (⟨v, hv⟩ : ↥C)⁻¹ := rfl
      rw [h1, map_mul, map_inv, toAdd_mul, toAdd_inv,
        hφ _ ⟨v, hv⟩ ⟨ρ (rootElt 1 2 s) v, hCinv _ v hv⟩ rfl, rootElt_mulVec (by decide)]
      simp
    have hrL : (r : V) ∈ L := hL (hD ▸ hrR)
    obtain ⟨hrC, hr0⟩ := hrL
    have : Multiplicative.toAdd (φ r) 0 = 0 := hr0
    rw [hφr] at this
    simp at this
  have hCle : C ≤ G6.submoduleClosure ρ.range R := by
    rw [← hC]
    refine commV_le_of_rootElt02 ρ _ (fun g s hs => rho_mem_submoduleClosure g hs)
      fun c v => ?_
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup.mp (hCZ ▸ Subgroup.mem_top v)
    have hzfix : ρ (rootElt 0 2 c) z = z := (mem_fixV_range.mp hz) _
    have he : ρ (rootElt 0 2 c) (a * z) * (a * z)⁻¹ = ρ (rootElt 0 2 c) a * a⁻¹ := by
      rw [map_mul, hzfix]
      group
    rw [he]
    exact le_submoduleClosure _ (G6.mem_commOn_of_mem (Subgroup.mem_map.mpr
      ⟨_, rootElt_mem_rootGroup 0 2 c, rfl⟩) ha)
  have hcardC : Nat.card C ≤ Nat.card F ^ 3 :=
    (Subgroup.card_le_of_le hCle).trans (card_closure_le h𝒲 hR hN hW2)
  have hq : Nat.card (↥C ⧸ φ.ker) = Nat.card F ^ 3 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      card_fin3_fun]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [hq] at hcard
  have hpos : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos 3
  have hker1 : Nat.card φ.ker = 1 := by
    have h1 : Nat.card F ^ 3 * Nat.card φ.ker ≤ Nat.card F ^ 3 * 1 := by
      rw [mul_one, ← hcard]; exact hcardC
    have h2 := Nat.le_of_mul_le_mul_left h1 hpos
    have h3 : 0 < Nat.card φ.ker := Nat.card_pos
    omega
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ hker1

end CFSG.Quasithin.MS93.M16
