module

public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.Monster.Existence

variable {G : Type} [Group G]

theorem cent_le_range_of_simple_cover {U : Type*} [Group U] (Φ : U →* G) {β : G}
    (hrange : Φ.range ≤ cent β) (hβ : β ∈ Φ.range)
    (hZ : (Subgroup.center (cent β)).map (cent β).subtype = Subgroup.zpowers β)
    (N : Subgroup U) [N.Normal] (hN : N ≤ (Subgroup.zpowers β).comap Φ)
    [Finite (U ⧸ N)] [IsSimpleGroup (U ⧸ N)]
    (hcard : Nat.card (U ⧸ N) = Nat.card (cent β ⧸ Subgroup.center (cent β)))
    (hnt : ∃ u, Φ u ∉ Subgroup.zpowers β) :
    cent β ≤ Φ.range := by
  have hZiff : ∀ z : cent β, z ∈ Subgroup.center (cent β) ↔ (z : G) ∈ Subgroup.zpowers β := by
    intro z
    constructor
    · intro hz
      rw [← hZ]
      exact ⟨z, hz, rfl⟩
    · intro hz
      rw [← hZ] at hz
      obtain ⟨z', hz', hzz⟩ := hz
      have : z' = z := Subtype.ext hzz
      rwa [this] at hz'
  let Φ' : U →* cent β := Φ.codRestrict (cent β) fun u => hrange ⟨u, rfl⟩
  let ψ₀ : U →* cent β ⧸ Subgroup.center (cent β) := (QuotientGroup.mk' _).comp Φ'
  have hker : N ≤ ψ₀.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 ((hZiff (Φ' n)).2 (hN hn))
  let ψ : U ⧸ N →* cent β ⧸ Subgroup.center (cent β) := QuotientGroup.lift N ψ₀ hker
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases Subgroup.Normal.eq_bot_or_eq_top ψ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu⟩ := hnt
      have hmem : (QuotientGroup.mk u : U ⧸ N) ∈ ψ.ker := by
        rw [h]
        exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hmem
      have h1 : ((Φ' u : cent β) : cent β ⧸ Subgroup.center (cent β)) = 1 := hmem
      exact hu ((hZiff (Φ' u)).1 ((QuotientGroup.eq_one_iff _).1 h1))
  have hpos : 0 < Nat.card (U ⧸ N) := Nat.card_pos
  have hfin : Finite (cent β ⧸ Subgroup.center (cent β)) :=
    Nat.finite_of_card_ne_zero (by rw [← hcard]; exact hpos.ne')
  have hbij : Function.Bijective ψ := hinj.bijective_of_nat_card_le hcard.ge
  intro c hc
  obtain ⟨x, hx⟩ := hbij.2 (QuotientGroup.mk' (Subgroup.center (cent β)) ⟨c, hc⟩)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : QuotientGroup.mk' (Subgroup.center (cent β)) (Φ' u) =
      QuotientGroup.mk' (Subgroup.center (cent β)) ⟨c, hc⟩ := hx
  have h2 : (Φ' u)⁻¹ * ⟨c, hc⟩ ∈ Subgroup.center (cent β) := QuotientGroup.eq.1 h1
  have h3 : (((Φ' u)⁻¹ * ⟨c, hc⟩ : cent β) : G) ∈ Φ.range :=
    Subgroup.zpowers_le.2 hβ ((hZiff _).1 h2)
  have h4 : c = Φ u * (((Φ' u)⁻¹ * ⟨c, hc⟩ : cent β) : G) := by
    have : Φ' u * ((Φ' u)⁻¹ * ⟨c, hc⟩) = ⟨c, hc⟩ := mul_inv_cancel_left _ _
    exact congrArg Subtype.val this.symm
  rw [h4]
  exact Φ.range.mul_mem ⟨u, rfl⟩ h3

end CFSG.Monster.Existence
