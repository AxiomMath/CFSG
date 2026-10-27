module

public import CFSG.Quasithin.Background.FixVZPowers
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.B4L3Inv

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def IsIndecompModule (G : Subgroup (MulAut V)) : Prop :=
  ∀ X Y : Subgroup V, (∀ g ∈ G, ∀ x ∈ X, g x ∈ X) → (∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y) →
    X ⊓ Y = ⊥ → X ⊔ Y = ⊤ → X = ⊥ ∨ Y = ⊥

section FactA

variable [Finite V] {G : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data G U Z)

include D in
theorem bounds_of_one_transvection (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    {a : MulAut V} (ha : a ∈ G) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hfix : Nat.card (fixV (Subgroup.zpowers a)) = 8) :
    Nat.card (commV G) ≤ 8 ∧ Nat.card V ≤ 8 * Nat.card (fixV G) := by
  have hconj : ∀ γ : L3.Γ, L3.IsInvol γ → Nat.card (fixV (Subgroup.zpowers (D.rho γ))) = 8 := by
    intro γ hγ
    have hmem : D.rho γ ∈ G := D.rho_mem γ
    have hsq : D.rho γ ^ 2 = 1 := by
      rw [pow_two, ← map_mul, hγ.1, map_one]
    have hne : D.rho γ ≠ 1 := by
      intro h
      apply hγ.2
      apply D.rho_injective
      rw [h, map_one]
    obtain ⟨g, -, hg⟩ := D.exists_conj ha ha2 ha1 hmem hsq hne
    rw [← hg, card_fixV_zpowers_conj]
    exact hfix
  exact bounds_of_transvections hV hcard (fun S h1 h2 h3 => D.le_of_gens h1 h2 h3)
    (hconj _ L3.x12_invol) (hconj _ L3.x23_invol) (hconj _ L3.x31_invol)

theorem card_fixV_involution_cases (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    {a : MulAut V} (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Nat.card (fixV (Subgroup.zpowers a)) = 4 ∨ Nat.card (fixV (Subgroup.zpowers a)) = 8 := by
  have h1 := card_commV_mul_card_fixV hV a
  have h2 : Nat.card (commV (Subgroup.zpowers a)) ≤ Nat.card (fixV (Subgroup.zpowers a)) :=
    Subgroup.card_le_of_le (commV_zpowers_le_fixV_b4 hV ha2)
  have h3 : commV (Subgroup.zpowers a) ≠ ⊥ := fun h => ha1 (commV_zpowers_eq_bot_iff.mp h)
  have h4 : 1 < Nat.card (commV (Subgroup.zpowers a)) := by
    by_contra h
    apply h3
    rw [Subgroup.eq_bot_iff_card]
    have := Nat.card_pos (α := ↥(commV (Subgroup.zpowers a)))
    omega
  rw [hcard] at h1
  have h5 : Nat.card (commV (Subgroup.zpowers a)) ∣ 16 := ⟨_, h1.symm⟩
  have h6 : Nat.card (commV (Subgroup.zpowers a)) ≤ 4 := by
    by_contra h
    push Not at h
    have : Nat.card (commV (Subgroup.zpowers a)) * Nat.card (commV (Subgroup.zpowers a)) ≤ 16 := by
      calc _ ≤ Nat.card (commV (Subgroup.zpowers a)) * Nat.card (fixV (Subgroup.zpowers a)) :=
            Nat.mul_le_mul_left _ h2
        _ = 16 := h1
    nlinarith
  have h7 : Nat.card (commV (Subgroup.zpowers a)) = 2 ∨ Nat.card (commV (Subgroup.zpowers a)) = 4 ∨
      Nat.card (commV (Subgroup.zpowers a)) = 3 := by omega
  rcases h7 with h | h | h
  · right; rw [h] at h1; omega
  · left; rw [h] at h1; omega
  · rw [h] at h5; omega

omit [Finite V] in
theorem commV_invariant (G : Subgroup (MulAut V)) : ∀ g ∈ G, ∀ x ∈ commV G, g x ∈ commV G := by
  have hG : G ≤ centQuot (commV G) := fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩
  intro g hg x hx
  exact (centQuot_le_stabSub _ (hG hg) x).2 hx

omit [Finite V] in
theorem fixV_invariant (G : Subgroup (MulAut V)) : ∀ g ∈ G, ∀ x ∈ fixV G, g x ∈ fixV G := by
  intro g hg x hx
  rw [hx g hg]
  exact hx

omit [Finite V] in
theorem commV_ne_bot_of_mem {G : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ G) (ha1 : a ≠ 1) :
    commV G ≠ ⊥ := by
  intro h
  apply ha1
  apply commV_zpowers_eq_bot_iff.mp
  rw [eq_bot_iff, ← h]
  unfold commV
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, v, rfl⟩
  exact ⟨x, (Subgroup.zpowers_le.mpr ha) hx, v, rfl⟩

include D in
theorem card_fixV_involution_two (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hU : U = ⊤) (hZ : Z = fixV G) (hind : IsIndecompModule G)
    {a : MulAut V} (ha : a ∈ G) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Nat.card (fixV (Subgroup.zpowers a)) = 4 := by
  rcases card_fixV_involution_cases hV hcard ha1 ha2 with h | h
  · exact h
  exfalso
  obtain ⟨hb1, hb2⟩ := bounds_of_one_transvection D hV hcard ha ha1 ha2 h
  have hU8 := D.card_U
  rw [hU, Subgroup.card_top, hcard, hZ] at hU8
  have hF2 : Nat.card (fixV G) = 2 := by omega
  have hcomm : ∀ w : L3.Vec, ∃ x ∈ commV G, ∃ hx : x ∈ U,
      D.β ⟨x, hx⟩ = Multiplicative.ofAdd w := by
    intro w
    obtain ⟨g, v', hgv⟩ := L3.act_allcomm w
    obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd v')
    have hmem : D.rho g (u : V) ∈ U := D.inv_U _ (D.rho_mem g) _ u.2
    refine ⟨D.rho g (u : V) * (u : V)⁻¹, Subgroup.subset_closure ⟨D.rho g, D.rho_mem g, u, rfl⟩,
      U.mul_mem hmem (U.inv_mem u.2), ?_⟩
    have h1 : (⟨D.rho g (u : V) * (u : V)⁻¹, U.mul_mem hmem (U.inv_mem u.2)⟩ : ↥U) =
        ⟨D.rho g (u : V), hmem⟩ * u⁻¹ := rfl
    rw [h1, map_mul, map_inv, D.β_rho g (u : V) u.2 hmem]
    have : (⟨(u : V), u.2⟩ : ↥U) = u := rfl
    rw [this, hu]
    show Multiplicative.ofAdd (L3.act g v') * (Multiplicative.ofAdd v')⁻¹ = Multiplicative.ofAdd w
    rw [← hgv, ofAdd_sub, div_eq_mul_inv]
    rfl
  have hsup : commV G ⊔ fixV G = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, hx, hxU, hβ⟩ := hcomm (Multiplicative.toAdd (D.β ⟨v, by rw [hU]; trivial⟩))
    have hvx : v * x⁻¹ ∈ fixV G := by
      rw [← hZ]
      rw [← D.ker_β ⟨v * x⁻¹, by rw [hU]; trivial⟩]
      have h1 : (⟨v * x⁻¹, by rw [hU]; trivial⟩ : ↥U) = ⟨v, by rw [hU]; trivial⟩ * ⟨x, hxU⟩⁻¹ := rfl
      rw [h1, map_mul, map_inv, hβ]
      exact mul_inv_cancel _
    have : v = (v * x⁻¹) * x := by group
    rw [this]
    exact Subgroup.mul_mem_sup hx hvx |> fun h => by
      simpa [sup_comm] using (Subgroup.mul_mem_sup hvx hx)
  have hinf : commV G ⊓ fixV G = ⊥ := by
    have h1 := card_sup_mul_card_inf (commV G) (fixV G)
    rw [hsup, Subgroup.card_top, hcard, hF2] at h1
    have h2 : Nat.card ↥(commV G ⊓ fixV G) = 1 := by
      have : Nat.card ↥(commV G ⊓ fixV G) ≤ 1 := by nlinarith
      have hpos : 0 < Nat.card ↥(commV G ⊓ fixV G) := Nat.card_pos
      omega
    exact Subgroup.card_eq_one.mp h2
  rcases hind (commV G) (fixV G) (commV_invariant G) (fixV_invariant G) hinf hsup with h | h
  · exact commV_ne_bot_of_mem ha ha1 h
  · rw [h, Subgroup.card_bot] at hF2
    omega

include D in
theorem card_fixV_involution_three (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hZ : Z = ⊥) (hind : IsIndecompModule G)
    {a : MulAut V} (ha : a ∈ G) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Nat.card (fixV (Subgroup.zpowers a)) = 4 := by
  rcases card_fixV_involution_cases hV hcard ha1 ha2 with h | h
  · exact h
  exfalso
  obtain ⟨hb1, hb2⟩ := bounds_of_one_transvection D hV hcard ha ha1 ha2 h
  have hU8 := D.card_U
  rw [hZ, Subgroup.card_bot] at hU8
  have hF : 2 ≤ Nat.card (fixV G) := by omega
  have hinf : U ⊓ fixV G = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huU, huF⟩
    rw [Subgroup.mem_bot]
    have hb : D.β ⟨u, huU⟩ = 1 := by
      have hfix : ∀ γ : L3.Γ, L3.act γ (Multiplicative.toAdd (D.β ⟨u, huU⟩)) =
          Multiplicative.toAdd (D.β ⟨u, huU⟩) := by
        intro γ
        have hmem : D.rho γ u ∈ U := D.inv_U _ (D.rho_mem γ) _ huU
        have h1 := D.β_rho γ u huU hmem
        have h2 : (⟨D.rho γ u, hmem⟩ : ↥U) = ⟨u, huU⟩ := Subtype.ext (huF _ (D.rho_mem γ))
        rw [h2] at h1
        have h3 := congrArg Multiplicative.toAdd h1
        exact h3.symm
      by_contra hne
      have hne' : Multiplicative.toAdd (D.β ⟨u, huU⟩) ≠ 0 := fun h0 => hne (by
        have : D.β ⟨u, huU⟩ = Multiplicative.ofAdd (Multiplicative.toAdd (D.β ⟨u, huU⟩)) := rfl
        rw [this, h0]; rfl)
      obtain ⟨γ, hγ⟩ := L3.act_nofix _ hne'
      exact hγ (hfix γ)
    have hz : u ∈ Z := (D.ker_β ⟨u, huU⟩).1 hb
    rw [hZ] at hz
    exact Subgroup.mem_bot.mp hz
  have hsup : U ⊔ fixV G = ⊤ := by
    have h1 := card_sup_mul_card_inf U (fixV G)
    rw [hinf, Subgroup.card_bot, mul_one, hU8] at h1
    have hle : Nat.card ↥(U ⊔ fixV G) ≤ Nat.card V := by
      simpa using Subgroup.card_le_of_le (le_top : (U ⊔ fixV G) ≤ ⊤)
    apply Subgroup.eq_top_of_card_eq
    omega
  have hUinv : ∀ g ∈ G, ∀ x ∈ U, g x ∈ U := fun g hg x hx => D.inv_U g hg x hx
  rcases hind U (fixV G) hUinv (fixV_invariant G) hinf hsup with h | h
  · rw [h, Subgroup.card_bot] at hU8
    omega
  · rw [h, Subgroup.card_bot] at hF
    omega

end FactA

end CFSG.Quasithin
