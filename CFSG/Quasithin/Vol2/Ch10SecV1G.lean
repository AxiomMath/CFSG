module

public import CFSG.Quasithin.Vol2.Ch10SecV1F
public import CFSG.Quasithin.Vol2.Ch10SecV1C

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {W₂ W₁ : Subgroup V}

theorem card_le_four_of_sq_le (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup V}
    (h : Nat.card X * Nat.card X ≤ 32) : Nat.card X ≤ 4 := by
  rw [card_eq_two_pow hV X] at h ⊢
  rcases Nat.lt_or_ge (rk X) 3 with hlt | hge
  · interval_cases (rk X) <;> norm_num
  · have : 2 ^ 3 ≤ 2 ^ rk X := Nat.pow_le_pow_right (by norm_num) hge
    nlinarith

theorem card_of_two (hV : ∀ v : V, v ^ 2 = 1) (D : L3Data G W₂ W₁) {U C₀ : Subgroup V}
    (hUc : ∀ g ∈ G, ∀ v, g v * v⁻¹ ∈ U) (hUU : U ≤ commSub U G) (hU16 : Nat.card U = 16)
    (hC₀U : C₀ ≤ U) (hC₀F : C₀ ≤ fixV G) (hC₀2 : Nat.card C₀ = 2) (hUFC : U ⊓ fixV G ≤ C₀)
    (hind : IsIndecompModule G) : Nat.card V = 16 := by
  have hinv : ∀ A : Subgroup V, U ≤ A → ∀ g ∈ G, ∀ a ∈ A, g a ∈ A := by
    intro A hUA g hg a ha
    have e : g a = (g a * a⁻¹) * a := by group
    rw [e]
    exact A.mul_mem (hUA (hUc g hg a)) ha
  have ht : ∀ v, D.rho L3.x12 (D.rho L3.x12 v) = v := rho_invol D L3.x12_invol
  have htU : ∀ u ∈ U, D.rho L3.x12 u ∈ U := hinv U le_rfl _ (D.rho_mem _)
  have hcU : Nat.card ↥(U.map (commHom (D.rho L3.x12)) ⊔ ⊥) = 4 := by
    have hsq := sq_bound D hV (hinv U le_rfl) bot_le bot_le
    rw [pow_two, hU16, Subgroup.card_bot] at hsq
    have h2 : 2 * Nat.card (⊥ : Subgroup V) < Nat.card ↥(U.map (commHom (D.rho L3.x12)) ⊔ ⊥) := by
      by_contra h
      have hb := comm_bound D (hinv U le_rfl) bot_le bot_le (not_lt.mp h)
      have hle := Subgroup.card_le_of_le (hUU.trans (le_sup_left : commSub U G ≤ _ ⊔ ⊥))
      rw [Subgroup.card_bot] at hb
      omega
    have := card_eq_four_mul hV le_sup_right h2 (by rw [Subgroup.card_bot]; omega)
    rwa [Subgroup.card_bot, mul_one] at this
  have hfU := card_sup_mul_card_fixRel (D.rho L3.x12) U ⊥
  rw [hcU, hU16, Subgroup.card_bot] at hfU
  have hleU := map_sup_le_fixRel hV ht htU bot_le
    (fun _ hk => by rw [Subgroup.mem_bot.mp hk, map_one])
  have heqU := Subgroup.eq_of_le_of_card_ge hleU (by omega)
  have hC₀t : C₀ ≤ U.map (commHom (D.rho L3.x12)) := by
    intro c hc
    have hcf : c ∈ fixRel (D.rho L3.x12) U ⊥ := by
      refine ⟨hC₀U hc, ?_⟩
      change D.rho L3.x12 c * c⁻¹ ∈ (⊥ : Subgroup V)
      rw [hC₀F hc _ (D.rho_mem _), mul_inv_cancel]
      exact Subgroup.one_mem _
    rw [← heqU, sup_bot_eq] at hcf
    exact hcf
  have hUF : U ⊔ fixV G = ⊤ := by
    by_contra h1
    obtain ⟨w, hw⟩ := exists_not_mem_of_ne_top h1
    have hwU : w ∉ U := fun h => hw (Subgroup.mem_sup_left h)
    have h32 : Nat.card ↥(U ⊔ Subgroup.zpowers w) = 32 := by
      rw [card_sup_zpowers hV hwU, hU16]
    have hinv' := hinv _ (le_sup_left : U ≤ U ⊔ Subgroup.zpowers w)
    have h4 : 2 * Nat.card C₀ <
        Nat.card ↥((U ⊔ Subgroup.zpowers w).map (commHom (D.rho L3.x12)) ⊔ C₀) := by
      by_contra hc
      obtain ⟨X, hXV, hX8, hX⟩ := fix_bound D hinv' hC₀F (not_lt.mp hc)
      have hXC : X ≤ C₀ := by
        intro x hx
        have hxF : x ∈ fixV G := mem_fixV_of_forall D hC₀F (hX x hx)
        rcases (mem_sup_zpowers_iff hV).mp (hXV hx) with h | h
        · exact hUFC ⟨h, hxF⟩
        · refine (hw ?_).elim
          have e : w = (x * w) * x⁻¹ := by rw [mul_comm x w, mul_inv_cancel_right]
          rw [e]
          exact Subgroup.mul_mem_sup h ((fixV G).inv_mem hxF)
      have := Subgroup.card_le_of_le hXC
      omega
    have hsq := sq_bound D hV hinv' bot_le bot_le
    rw [pow_two, h32, Subgroup.card_bot, sup_bot_eq] at hsq
    have hV4 := card_le_four_of_sq_le hV (by omega : Nat.card ↥((U ⊔ Subgroup.zpowers w).map
      (commHom (D.rho L3.x12))) * Nat.card ↥((U ⊔ Subgroup.zpowers w).map
        (commHom (D.rho L3.x12))) ≤ 32)
    have hsi := card_sup_mul_card_inf ((U ⊔ Subgroup.zpowers w).map (commHom (D.rho L3.x12))) C₀
    rw [hC₀2] at hsi h4
    have hi1 : Nat.card ↥((U ⊔ Subgroup.zpowers w).map (commHom (D.rho L3.x12)) ⊓ C₀) = 1 := by
      have hpos : 0 < Nat.card ↥((U ⊔ Subgroup.zpowers w).map (commHom (D.rho L3.x12)) ⊓ C₀) :=
        Nat.card_pos
      nlinarith
    have hmono : U.map (commHom (D.rho L3.x12)) ≤
        (U ⊔ Subgroup.zpowers w).map (commHom (D.rho L3.x12)) := Subgroup.map_mono le_sup_left
    rw [sup_bot_eq] at hcU
    have heq := Subgroup.eq_of_le_of_card_ge hmono (by omega)
    have hC₀le : C₀ ≤ (U ⊔ Subgroup.zpowers w).map (commHom (D.rho L3.x12)) ⊓ C₀ :=
      le_inf (heq ▸ hC₀t) le_rfl
    have := Subgroup.card_le_of_le hC₀le
    omega
  obtain ⟨B, hBF, hinf, hsup⟩ := exists_compl hV (inf_le_right : U ⊓ fixV G ≤ fixV G)
  have hUB : U ⊓ B = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    rintro x ⟨hxU, hxB⟩
    exact ⟨⟨hxU, hBF hxB⟩, hxB⟩
  have hUB' : U ⊔ B = ⊤ := by
    rw [← hUF, ← hsup, ← sup_assoc, sup_inf_self]
  have hBinv : ∀ g ∈ G, ∀ b ∈ B, g b ∈ B := fun g hg b hb => by rw [hBF hb g hg]; exact hb
  rcases hind U B (hinv U le_rfl) hBinv hUB hUB' with h | h
  · rw [h, Subgroup.card_bot] at hU16
    omega
  · rw [h, sup_bot_eq] at hUB'
    rw [← Subgroup.card_top (G := V), ← hUB', hU16]

end CFSG.Quasithin.Vol2.Ch10.V1C
