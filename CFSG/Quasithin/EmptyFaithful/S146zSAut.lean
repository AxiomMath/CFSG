module

public import CFSG.Quasithin.EmptyFaithful.S146zRL3Case

public section

namespace CFSG.Quasithin

open CFSG.Open

section Pure

variable {X : Type} [Group X] [Finite X] {N₁ N₂ : Subgroup X} {ŝ : X}

theorem q_index_dvd_of_card_aut_pow (hF : CaseIFacts N₁ N₂ ŝ)
    (hbot : N₁ ≠ ⊥) {k : ℕ} (hA : Nat.card (MulAut ↥N₁) = 2 ^ k * Nat.card ↥N₁) :
    (N₁ ⊔ N₂).index ∣ 2 ^ (2 * k + 1) := by
  classical
  have hne := q_ne_pair hF hbot
  obtain ⟨σ, hσs, hσ⟩ := QWr.exists_sigma hF.conj hne hF.perm
  have hX₀ : ∀ x, x ∈ σ.ker ↔ N₁.map (MulAut.conj x).toMonoidHom = N₁ := fun x => by
    rw [MonoidHom.mem_ker]
    exact hσ x
  have hidx : σ.ker.index ∣ 2 := by
    rw [Subgroup.index_ker]
    have h1 := Subgroup.card_subgroup_dvd_card σ.range
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      exact Nat.card_zmod 2
    rwa [h2] at h1
  have hN₁X₀ : ∀ x ∈ σ.ker, x ∈ Subgroup.normalizer (N₁ : Set X) := fun x hx =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr ((hX₀ x).mp hx)
  have hN₂X₀ : ∀ x ∈ σ.ker, x ∈ Subgroup.normalizer (N₂ : Set X) := by
    intro x hx
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rcases QWr.conj_N₂_cases hF.conj hF.perm x with h | h
    · exact absurd (QWr.map_conj_injective x (((hX₀ x).mp hx).trans h.symm)) hne
    · exact h
  let ν : ↥σ.ker →* MulAut ↥N₁ × MulAut ↥N₂ :=
    ((N₁.normalizerMonoidHom).comp (Subgroup.inclusion (fun x hx => hN₁X₀ x hx) :
        ↥σ.ker →* ↥(Subgroup.normalizer (N₁ : Set X)))).prod
      ((N₂.normalizerMonoidHom).comp (Subgroup.inclusion (fun x hx => hN₂X₀ x hx) :
        ↥σ.ker →* ↥(Subgroup.normalizer (N₂ : Set X))))
  have hν : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : N₁.normalizerMonoidHom ⟨(x : X), hN₁X₀ x x.2⟩ = 1 := congrArg Prod.fst hx
    have h2 : N₂.normalizerMonoidHom ⟨(x : X), hN₂X₀ x x.2⟩ = 1 := congrArg Prod.snd hx
    have hc₁ : ∀ n ∈ N₁, (x : X) * n = n * (x : X) := fun n hn => by
      have := Subgroup.normalizerMonoidHom_apply_apply_coe N₁ ⟨(x : X), hN₁X₀ x x.2⟩ ⟨n, hn⟩
      rw [h1] at this
      simp only [MulAut.one_apply] at this
      calc (x : X) * n = (x : X) * n * (x : X)⁻¹ * (x : X) := by group
        _ = n * (x : X) := by rw [← this]
    have hc₂ : ∀ n ∈ N₂, (x : X) * n = n * (x : X) := fun n hn => by
      have := Subgroup.normalizerMonoidHom_apply_apply_coe N₂ ⟨(x : X), hN₂X₀ x x.2⟩ ⟨n, hn⟩
      rw [h2] at this
      simp only [MulAut.one_apply] at this
      calc (x : X) * n = (x : X) * n * (x : X)⁻¹ * (x : X) := by group
        _ = n * (x : X) := by rw [← this]
    exact Subtype.ext (q_eq_one_of_centralizes hF hc₁ hc₂)
  have hAut₂ : Nat.card (MulAut ↥N₂) = Nat.card (MulAut ↥N₁) := by
    let e : ↥N₁ ≃* ↥N₂ :=
      (N₁.equivMapOfInjective (MulAut.conj ŝ).toMonoidHom (MulAut.conj ŝ).injective).trans
        (MulEquiv.subgroupCongr hF.conj.symm)
    exact (Nat.card_congr (MulAut.congr e).toEquiv).symm
  have hd1 : Nat.card ↥σ.ker ∣ Nat.card (MulAut ↥N₁) * Nat.card (MulAut ↥N₂) := by
    have := Subgroup.card_dvd_of_injective ν hν
    rwa [Nat.card_prod] at this
  rw [hAut₂, hA] at hd1
  have hn : 0 < Nat.card ↥N₁ := Nat.card_pos
  have hd2 : Nat.card ↥σ.ker ∣ 2 ^ (2 * k) * Nat.card ↥N₁ ^ 2 := by
    have : 2 ^ k * Nat.card ↥N₁ * (2 ^ k * Nat.card ↥N₁) = 2 ^ (2 * k) * Nat.card ↥N₁ ^ 2 := by
      ring
    rwa [this] at hd1
  have hX : Nat.card X ∣ 2 ^ (2 * k + 1) * Nat.card ↥N₁ ^ 2 := by
    have h1 := Subgroup.index_mul_card σ.ker
    rw [← h1]
    have := Nat.mul_dvd_mul hidx hd2
    rwa [show 2 * (2 ^ (2 * k) * Nat.card ↥N₁ ^ 2) = 2 ^ (2 * k + 1) * Nat.card ↥N₁ ^ 2 by
      ring] at this
  have h1 := Subgroup.index_mul_card (N₁ ⊔ N₂)
  rw [q_card_sup_pair hF] at h1
  rw [← h1] at hX
  have hpos : 0 < Nat.card ↥N₁ ^ 2 := pow_pos hn 2
  have : (N₁ ⊔ N₂).index * Nat.card ↥N₁ ^ 2 ∣ 2 ^ (2 * k + 1) * Nat.card ↥N₁ ^ 2 := hX
  exact Nat.dvd_of_mul_dvd_mul_right hpos this

end Pure

end CFSG.Quasithin
