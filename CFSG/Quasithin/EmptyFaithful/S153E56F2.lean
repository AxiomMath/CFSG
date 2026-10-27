module

public import CFSG.Quasithin.EmptyFaithful.S153E55D

public section

namespace CFSG.Quasithin

namespace S153E56f

open CFSG.QuasithinUnique

section Elementary

private theorem perm_inv_aux : ∀ a p : Equiv.Perm (Fin 3), a * a = 1 → a ≠ 1 → p ^ 3 = 1 → p ≠ 1 →
    a * p * a⁻¹ = p⁻¹ := by
  decide +kernel

private theorem perm_pow_nine : ∀ σ : Equiv.Perm (Fin 3), σ ^ 9 = 1 → σ ^ 3 = 1 := by
  decide +kernel

theorem eq_one_of_sq_cube {α : Type*} [Group α] {p : α} (h2 : p * p = 1) (h3 : p ^ 3 = 1) :
    p = 1 := by
  rw [pow_three, h2, mul_one] at h3
  exact h3

theorem odd_orderOf_of_pow_three {α : Type*} [Group α] {p : α} (h3 : p ^ 3 = 1) :
    Odd (orderOf p) := by
  have : orderOf p ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h
  · rw [h]
    exact ⟨0, rfl⟩
  · rw [h]
    exact ⟨1, rfl⟩

theorem lift_calc {α : Type*} [Group α] {a p : α} (haa : a * a = 1) (hapa : a * p * a⁻¹ = p⁻¹)
    (hp3 : p ^ 3 = 1) : (a * (p⁻¹ * a * p)) ^ 2 = p := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have h1 : a * p⁻¹ * a = p := by
    have := congrArg (fun x => x⁻¹) hapa
    simp only [mul_inv_rev, inv_inv, ha'] at this
    simpa [mul_assoc] using this
  have h2 : a * (p⁻¹ * a * p) = p * p := by
    calc a * (p⁻¹ * a * p) = (a * p⁻¹ * a) * p := by group
      _ = p * p := by rw [h1]
  rw [h2]
  have : (p * p) ^ 2 = p * p ^ 3 := by
    rw [pow_two, pow_three]
    simp only [mul_assoc]
  rw [this, hp3, mul_one]

variable {W : Type} [CommGroup W]

theorem card_eq_six {N : Subgroup (MulAut W)} (e : ↥N ≃* Equiv.Perm (Fin 3)) : Nat.card N = 6 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem exists_order_three {N : Subgroup (MulAut W)} (e : ↥N ≃* Equiv.Perm (Fin 3)) :
    ∃ p ∈ N, p ^ 3 = 1 ∧ p ≠ 1 := by
  refine ⟨((e.symm (finRotate 3) : ↥N) : MulAut W), (e.symm (finRotate 3)).2, ?_, ?_⟩
  · have h : (e.symm (finRotate 3)) ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      simp only [MulEquiv.apply_symm_apply]
      decide
    simpa using congrArg Subtype.val h
  · intro h
    have h1 : e.symm (finRotate 3) = 1 := Subtype.ext h
    have h2 := congrArg e h1
    simp only [MulEquiv.apply_symm_apply, map_one] at h2
    exact absurd h2 (by decide)

theorem inv_of_invol {N : Subgroup (MulAut W)} (e : ↥N ≃* Equiv.Perm (Fin 3)) {a p : MulAut W}
    (haN : a ∈ N) (hpN : p ∈ N) (ha : a * a = 1) (ha1 : a ≠ 1) (hp : p ^ 3 = 1) (hp1 : p ≠ 1) :
    a * p * a⁻¹ = p⁻¹ := by
  have key := perm_inv_aux (e ⟨a, haN⟩) (e ⟨p, hpN⟩) ?_ ?_ ?_ ?_
  · have h : e (⟨a, haN⟩ * ⟨p, hpN⟩ * ⟨a, haN⟩⁻¹) = e (⟨p, hpN⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv]
      exact key
    exact congrArg Subtype.val (e.injective h)
  · rw [← map_mul]
    have h : (⟨a, haN⟩ : ↥N) * ⟨a, haN⟩ = 1 := Subtype.ext ha
    rw [h, map_one]
  · intro h
    apply ha1
    exact congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
  · rw [← map_pow]
    have h : (⟨p, hpN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hp)
    rw [h, map_one]
  · intro h
    apply hp1
    exact congrArg Subtype.val (e.injective (h.trans (map_one e).symm))

theorem pow_three_of_pow_nine {N : Subgroup (MulAut W)} (e : ↥N ≃* Equiv.Perm (Fin 3))
    {p : MulAut W} (hpN : p ∈ N) (h9 : p ^ 9 = 1) : p ^ 3 = 1 := by
  have h1 : (e ⟨p, hpN⟩) ^ 9 = 1 := by
    rw [← map_pow]
    have h : (⟨p, hpN⟩ : ↥N) ^ 9 = 1 := Subtype.ext (by simpa using h9)
    rw [h, map_one]
  have h2 := perm_pow_nine _ h1
  have h3 : (⟨p, hpN⟩ : ↥N) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, h2, map_one]
  simpa using congrArg Subtype.val h3

end Elementary

section Klein

variable {W : Type} [CommGroup W]

theorem exists_ab [Finite W] {N₁ N₂ Ub : Subgroup (MulAut W)} (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hinf : N₁ ⊓ N₂ = ⊥) (h₁ : Nat.card N₁ = 6) (h₂ : Nat.card N₂ = 6)
    (hS : IsSylowTwoOf Ub (N₁ ⊔ N₂)) :
    ∃ a b : MulAut W, a ∈ Ub ∧ b ∈ Ub ∧ a ∈ N₁ ∧ b ∈ N₂ ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * a = 1 ∧ b * b = 1 ∧
      ∀ x ∈ Ub, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hJcard : Nat.card ↥(N₁ ⊔ N₂) = 36 := by
    have := B2F.card_sup_mul_card_inf_of_commute hc
    rw [hinf, Subgroup.card_bot, mul_one, h₁, h₂] at this
    omega
  have hScard : Nat.card Ub = 4 := S1417.card_eq_four_of_isSylowTwoOf hS hJcard
  have hn₁ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₁ : Set (MulAut W)) := by
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    exact Subgroup.centralizer_le_normalizer (s := (N₁ : Set (MulAut W)))
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb)
  have hn₂ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₂ : Set (MulAut W)) := by
    refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer (s := (N₂ : Set (MulAut W)))
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)
  have hS₁ : IsSylowTwoOf (Ub ⊓ N₁) N₁ := A4.isSylowTwoOf_inf_normal hS le_sup_left hn₁
  have hS₂ : IsSylowTwoOf (Ub ⊓ N₂) N₂ := A4.isSylowTwoOf_inf_normal hS le_sup_right hn₂
  have hS₁card : Nat.card ↥(Ub ⊓ N₁) = 2 := S1417.card_eq_two_of_isSylowTwoOf hS₁ h₁
  have hS₂card : Nat.card ↥(Ub ⊓ N₂) = 2 := S1417.card_eq_two_of_isSylowTwoOf hS₂ h₂
  obtain ⟨a, hamem, ha1, hau⟩ := S1417.exists_eq_of_card_eq_two hS₁card
  obtain ⟨b, hbmem, hb1, hbu⟩ := S1417.exists_eq_of_card_eq_two hS₂card
  have haa : a * a = 1 := by
    have := pow_card_eq_one' (G := ↥(Ub ⊓ N₁)) (x := ⟨a, hamem⟩)
    rw [hS₁card] at this
    have h' : a ^ 2 = 1 := congrArg Subtype.val this
    rwa [pow_two] at h'
  have hbb : b * b = 1 := by
    have := pow_card_eq_one' (G := ↥(Ub ⊓ N₂)) (x := ⟨b, hbmem⟩)
    rw [hS₂card] at this
    have h' : b ^ 2 = 1 := congrArg Subtype.val this
    rwa [pow_two] at h'
  have hcomm : ∀ x ∈ Ub ⊓ N₁, ∀ y ∈ Ub ⊓ N₂, x * y = y * x := fun x hx y hy => hc x hx.2 y hy.2
  have hSeq : Ub = (Ub ⊓ N₁) ⊔ (Ub ⊓ N₂) := by
    have hinf2 : (Ub ⊓ N₁) ⊓ (Ub ⊓ N₂) = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [← hinf]
      exact inf_le_inf inf_le_right inf_le_right
    have h1 := B2F.card_sup_mul_card_inf_of_commute hcomm
    rw [hinf2, Subgroup.card_bot, mul_one, hS₁card, hS₂card] at h1
    exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) (by omega)).symm
  refine ⟨a, b, hamem.1, hbmem.1, hamem.2, hbmem.2, ha1, hb1, haa, hbb, fun x hx => ?_⟩
  rw [hSeq] at hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := S153E55.mem_sup_of_comm hcomm hx
  rcases hau x₁ hx₁ with h1 | h1 <;> rcases hbu x₂ hx₂ with h2 | h2 <;> simp [h1, h2]

theorem exists_UbData [Finite W] {X N₁ N₂ Ub T' : Subgroup (MulAut W)} {r : MulAut W}
    (e₁ : ↥N₁ ≃* Equiv.Perm (Fin 3)) (e₂ : ↥N₂ ≃* Equiv.Perm (Fin 3))
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hinf : N₁ ⊓ N₂ = ⊥)
    (hS : IsSylowTwoOf Ub (N₁ ⊔ N₂)) (hN₁X : N₁ ≤ X) (hN₂X : N₂ ≤ X) (hUbT : Ub ≤ T')
    (hUbn : ∀ h ∈ T', ∀ n ∈ Ub, h * n * h⁻¹ ∈ Ub) (hUbc : ∀ a ∈ Ub, ∀ b ∈ Ub, a * b = b * a)
    (hidx : Ub.relIndex T' = 2) (hrUb : r ∈ Ub) (hr1 : r ≠ 1) (hrc : ∀ x ∈ T', x * r = r * x)
    (hrinv : ∀ y ∈ X, Odd (orderOf y) → r * y * r⁻¹ = y⁻¹)
    (hcen : ∀ z ∈ T', (∀ x ∈ T', x * z = z * x) → z = 1 ∨ z = r) :
    ∃ a b : MulAut W, a ∈ Ub ∧ b ∈ Ub ∧ a ∈ N₁ ∧ b ∈ N₂ ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * a = 1 ∧ b * b = 1 ∧
      (∀ x ∈ Ub, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ∧
      (∀ τ ∈ T', τ ∉ Ub → τ * a * τ⁻¹ = b ∧ τ * b * τ⁻¹ = a) := by
  obtain ⟨a, b, haU, hbU, haN, hbN, ha1, hb1, haa, hbb, hUb⟩ :=
    exists_ab hc hinf (card_eq_six e₁) (card_eq_six e₂) hS
  have hrne : ∀ {N N' : Subgroup (MulAut W)} (e' : ↥N' ≃* Equiv.Perm (Fin 3)), N' ≤ X →
      (∀ c ∈ N, ∀ p ∈ N', c * p = p * c) → ∀ c ∈ N, c ≠ r := by
    intro N N' e' hN'X hcomm c hcN hcr
    obtain ⟨p, hpN', hp3, hp1⟩ := exists_order_three e'
    have h1 : r * p * r⁻¹ = p := by
      rw [← hcr]
      calc c * p * c⁻¹ = p * c * c⁻¹ := by rw [hcomm c hcN p hpN']
        _ = p := by group
    have h2 : r * p * r⁻¹ = p⁻¹ := hrinv p (hN'X hpN') (odd_orderOf_of_pow_three hp3)
    have h3 : p * p = 1 := by
      rw [h1] at h2
      exact mul_eq_one_iff_eq_inv.mpr h2
    exact hp1 (eq_one_of_sq_cube h3 hp3)
  have hra : a ≠ r := hrne e₂ hN₂X hc a haN
  have hrb : b ≠ r :=
    hrne e₁ hN₁X (fun c hc' p hp' => (hc p hp' c hc').symm) b hbN
  have hrab : r = a * b := by
    rcases hUb r hrUb with h | h | h | h
    · exact absurd h hr1
    · exact absurd h.symm hra
    · exact absurd h.symm hrb
    · exact h
  have hUb₁ : ∀ x ∈ Ub, x = 1 ∨ x = a ∨ x = b ∨ x = r := fun x hx => by
    rw [hrab]
    exact hUb x hx
  have hUb₂ : ∀ x ∈ Ub, x = 1 ∨ x = b ∨ x = a ∨ x = r := fun x hx => by
    rcases hUb₁ x hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  have key : ∀ c d : MulAut W, c ∈ Ub → c ≠ 1 → c ≠ r →
      (∀ x ∈ Ub, x = 1 ∨ x = c ∨ x = d ∨ x = r) →
      ∀ τ ∈ T', τ ∉ Ub → τ * c * τ⁻¹ = d := by
    intro c d hcU hc1 hcr hcl τ hτ hτU
    have hmem : τ * c * τ⁻¹ ∈ Ub := hUbn τ hτ c hcU
    have hne1 : τ * c * τ⁻¹ ≠ 1 := by
      intro h
      apply hc1
      have : c = τ⁻¹ * (τ * c * τ⁻¹) * τ := by group
      rw [this, h]
      group
    have hner : τ * c * τ⁻¹ ≠ r := by
      intro h
      apply hcr
      have h' := hrc τ hτ
      have : c = τ⁻¹ * (τ * c * τ⁻¹) * τ := by group
      rw [this, h]
      calc τ⁻¹ * r * τ = τ⁻¹ * (r * τ) := by group
        _ = τ⁻¹ * (τ * r) := by rw [h']
        _ = r := by group
    have hnec : τ * c * τ⁻¹ ≠ c := by
      intro h
      have hcentral : ∀ x ∈ T', x * c = c * x := by
        intro x hx
        rcases coset_of_relIndex_two hidx hx hτ hτU with hxU | hxU
        · exact hUbc x hxU c hcU
        · have hτc : τ * c = c * τ := by
            calc τ * c = (τ * c * τ⁻¹) * τ := by group
              _ = c * τ := by rw [h]
          calc x * c = (x * τ⁻¹) * (τ * c) := by group
            _ = (x * τ⁻¹) * (c * τ) := by rw [hτc]
            _ = ((x * τ⁻¹) * c) * τ := by group
            _ = (c * (x * τ⁻¹)) * τ := by rw [hUbc _ hxU c hcU]
            _ = c * x := by group
      rcases hcen c (hUbT hcU) hcentral with h1 | h1
      · exact hc1 h1
      · exact hcr h1
    rcases hcl _ hmem with h | h | h | h
    · exact absurd h hne1
    · exact absurd h hnec
    · exact h
    · exact absurd h hner
  exact ⟨a, b, haU, hbU, haN, hbN, ha1, hb1, haa, hbb, hUb, fun τ hτ hτU =>
    ⟨key a b haU ha1 hra hUb₁ τ hτ hτU, key b a hbU hb1 hrb hUb₂ τ hτ hτU⟩⟩

theorem mem_N₂_of_inv {N₁ N₂ : Subgroup (MulAut W)} (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hinf : N₁ ⊓ N₂ = ⊥) {b w : MulAut W} (hbN : b ∈ N₂) (hw : w ∈ N₁ ⊔ N₂) (hw3 : w ^ 3 = 1)
    (hbw : b * w * b⁻¹ = w⁻¹) : w ∈ N₂ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := S153E55.mem_sup_of_comm hc hw
  have hcomm : Commute w₁ w₂ := hc w₁ hw₁ w₂ hw₂
  have h3 : w₁ ^ 3 * w₂ ^ 3 = 1 := by
    rw [← hcomm.mul_pow]
    exact hw3
  have hw₁3 : w₁ ^ 3 = 1 := by
    have hmem : w₁ ^ 3 ∈ N₁ ⊓ N₂ := by
      refine ⟨N₁.pow_mem hw₁ 3, ?_⟩
      have : w₁ ^ 3 = (w₂ ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
      rw [this]
      exact N₂.inv_mem (N₂.pow_mem hw₂ 3)
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hbw₁ : b * w₁ * b⁻¹ = w₁ := by
    have := hc w₁ hw₁ b hbN
    calc b * w₁ * b⁻¹ = w₁ * b * b⁻¹ := by rw [this]
      _ = w₁ := by group
  have hu : b * w₂ * b⁻¹ ∈ N₂ := N₂.mul_mem (N₂.mul_mem hbN hw₂) (N₂.inv_mem hbN)
  have hw₁c : ∀ n ∈ N₂, w₁ * n = n * w₁ := fun n hn => hc w₁ hw₁ n hn
  have hw₁2 : w₁ * w₁ = 1 := by
    have h1 : w₁ * (b * w₂ * b⁻¹) = w₁⁻¹ * w₂⁻¹ := by
      have e1 : b * (w₁ * w₂) * b⁻¹ = (b * w₁ * b⁻¹) * (b * w₂ * b⁻¹) := by group
      have e2 : (w₁ * w₂)⁻¹ = w₁⁻¹ * w₂⁻¹ := by
        rw [mul_inv_rev]
        exact hcomm.inv_inv.eq.symm
      rw [e1, e2, hbw₁] at hbw
      exact hbw
    have h2 : w₁ * w₁ = w₂⁻¹ * (b * w₂ * b⁻¹)⁻¹ := by
      have h4 : w₁ * (w₁ * (b * w₂ * b⁻¹)) = w₂⁻¹ := by
        rw [h1]
        group
      calc w₁ * w₁ = (w₁ * (w₁ * (b * w₂ * b⁻¹))) * (b * w₂ * b⁻¹)⁻¹ := by group
        _ = w₂⁻¹ * (b * w₂ * b⁻¹)⁻¹ := by rw [h4]
    have hmem : w₁ * w₁ ∈ N₁ ⊓ N₂ :=
      ⟨N₁.mul_mem hw₁ hw₁, by rw [h2]; exact N₂.mul_mem (N₂.inv_mem hw₂) (N₂.inv_mem hu)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  have : w₁ = 1 := eq_one_of_sq_cube hw₁2 hw₁3
  rw [this, one_mul]
  exact hw₂

end Klein

end S153E56f

end CFSG.Quasithin
