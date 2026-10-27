module

public import CFSG.Quasithin.H13.L32AC47f

public section

namespace CFSG.Quasithin.H13.A6.Hat6

open Equiv Equiv.Perm CFSG.Quasithin.H13.L32A.C.Alt6

section Gen

variable {W : Type*} [CommGroup W]

theorem const_of_rel_gen {N : Subgroup A6} {α β g₁ : A6} (w : A6 → W)
    (hN : ∀ g : A6, ∀ n ∈ N, w (g * n) = w g)
    (hrel : ∀ h g : A6, w g * w (h * α * h⁻¹ * g) * w (h * β * h⁻¹ * g) *
      w (h * β * h⁻¹ * (h * α * h⁻¹) * g) = 1)
    (hmatch : ∀ x : A6, w (x * (g₁ * α * g₁⁻¹)) * w (x * (g₁ * β * g₁⁻¹)) *
        w (x * (g₁ * β * g₁⁻¹ * (g₁ * α * g₁⁻¹))) =
      w (x * (α * g₁)) * w (x * (β * g₁)) * w (x * (β * α * g₁)))
    (hgen : N ⊔ Subgroup.zpowers g₁ = ⊤) (g : A6) : w g = w 1 := by
  have step : ∀ x : A6, w (x * g₁) = w x := by
    intro x
    have hb := hrel x (x * g₁)
    have ha := hrel (x * g₁) x
    have e1 : x * α * x⁻¹ * (x * g₁) = x * (α * g₁) := by group
    have e2 : x * β * x⁻¹ * (x * g₁) = x * (β * g₁) := by group
    have e3 : x * β * x⁻¹ * (x * α * x⁻¹) * (x * g₁) = x * (β * α * g₁) := by group
    have e4 : x * g₁ * α * (x * g₁)⁻¹ * x = x * (g₁ * α * g₁⁻¹) := by group
    have e5 : x * g₁ * β * (x * g₁)⁻¹ * x = x * (g₁ * β * g₁⁻¹) := by group
    have e6 : x * g₁ * β * (x * g₁)⁻¹ * (x * g₁ * α * (x * g₁)⁻¹) * x =
        x * (g₁ * β * g₁⁻¹ * (g₁ * α * g₁⁻¹)) := by group
    rw [e1, e2, e3] at hb
    rw [e4, e5, e6] at ha
    have ha' : w x * (w (x * (g₁ * α * g₁⁻¹)) * w (x * (g₁ * β * g₁⁻¹)) *
        w (x * (g₁ * β * g₁⁻¹ * (g₁ * α * g₁⁻¹)))) = 1 := by
      rw [← ha]
      simp only [mul_assoc]
    rw [hmatch x] at ha'
    have hb' : w (x * g₁) * (w (x * (α * g₁)) * w (x * (β * g₁)) * w (x * (β * α * g₁))) = 1 := by
      rw [← hb]
      simp only [mul_assoc]
    exact (mul_right_cancel (hb'.trans ha'.symm))
  let S : Subgroup A6 :=
    { carrier := {s | ∀ x : A6, w (x * s) = w x}
      one_mem' := fun x => by rw [mul_one]
      mul_mem' := fun {a b} ha hb x => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha x => by
        have h1 := ha (x * a⁻¹)
        rw [inv_mul_cancel_right] at h1
        exact h1.symm }
  have hS : N ⊔ Subgroup.zpowers g₁ ≤ S :=
    sup_le (fun n hn x => hN x n hn) ((Subgroup.zpowers_le).mpr step)
  rw [hgen] at hS
  have h1 := hS (Subgroup.mem_top g) 1
  rwa [one_mul] at h1

theorem sup_zpowers_eq_top {N : Subgroup A6} (hD : D0 ≤ N) {x : A6} (hxN : x ∈ N)
    (hx3 : orderOf x = 3) {g n : A6} (hnN : n ∈ N) (h5 : orderOf (n * g) = 5) :
    N ⊔ Subgroup.zpowers g = ⊤ := by
  set Y := N ⊔ Subgroup.zpowers g with hY
  have h8 : 8 ∣ Nat.card Y := card_D0 ▸ Subgroup.card_dvd_of_le (hD.trans le_sup_left)
  have hxY : x ∈ Y := Subgroup.mem_sup_left hxN
  have hgY : g ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have h3 : 3 ∣ Nat.card Y := by
    have ho : orderOf (⟨x, hxY⟩ : Y) = 3 := by rw [Subgroup.orderOf_mk, hx3]
    exact ho ▸ orderOf_dvd_natCard _
  have h5' : 5 ∣ Nat.card Y := by
    have ho : orderOf (⟨n * g, Y.mul_mem (Subgroup.mem_sup_left hnN) hgY⟩ : Y) = 5 := by
      rw [Subgroup.orderOf_mk, h5]
    exact ho ▸ orderOf_dvd_natCard _
  have h120 : 120 ∣ Nat.card Y :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by norm_num) h8 h3) h5'
  have hdvd : Nat.card Y ∣ 360 := card_A6 ▸ Subgroup.card_subgroup_dvd_card Y
  have hcases : Nat.card Y = 120 ∨ Nat.card Y = 360 := by
    obtain ⟨k, hk⟩ := h120
    have hk3 : k ∣ 3 := by
      obtain ⟨m, hm⟩ := hdvd
      have h1 : 120 * (k * m) = 120 * 3 := by rw [← mul_assoc, ← hk, ← hm]
      exact ⟨m, (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h | h <;> subst h <;> omega
  rcases hcases with h | h
  · exfalso
    have hidx : Y.index = 3 := by
      have := Y.card_mul_index
      rw [h, card_A6] at this
      omega
    have : Y.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
    have hd := Y.index_normalCore_dvd_factorial_index
    have hsimple : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with hb | ht
    · rw [hb, Subgroup.index_bot, card_A6, hidx] at hd
      exact absurd hd (by decide)
    · have : Y = ⊤ := eq_top_iff.mpr (ht ▸ Y.normalCore_le)
      rw [this, Subgroup.card_top, card_A6] at h
      omega
  · exact Subgroup.eq_top_of_card_eq Y (h.trans card_A6.symm)

end Gen

@[expose] def g1P : Perm (Fin 6) := swap 3 4 * swap 4 5

@[expose] def g2P : Perm (Fin 6) := swap 1 2 * swap 3 4

@[expose] def n1P : Perm (Fin 6) := swap 1 2 * swap 2 3

theorem g1_sign : Equiv.Perm.sign g1P = 1 := by decide +kernel

theorem n1_sign : Equiv.Perm.sign n1P = 1 := by decide +kernel

theorem g2_sign : Equiv.Perm.sign g2P = 1 := by decide +kernel

abbrev g1A : A6 := toA6 g1P g1_sign

abbrev n1A : A6 := toA6 n1P n1_sign

abbrev g2A : A6 := toA6 g2P g2_sign

theorem e1_c1 : ∀ e ∈ e1List, (((zA * g1A)⁻¹ * (g1A * zA * g1A⁻¹) : A6) : Perm (Fin 6)) * e *
    (((zA * g1A)⁻¹ * (g1A * zA * g1A⁻¹) : A6) : Perm (Fin 6))⁻¹ ∈ e1List := by
  decide +kernel

theorem e1_c2 : ∀ e ∈ e1List, (((aA * g1A)⁻¹ * (g1A * aA * g1A⁻¹) : A6) : Perm (Fin 6)) * e *
    (((aA * g1A)⁻¹ * (g1A * aA * g1A⁻¹) : A6) : Perm (Fin 6))⁻¹ ∈ e1List := by
  decide +kernel

theorem e1_c3 : ∀ e ∈ e1List,
    (((aA * zA * g1A)⁻¹ * (g1A * aA * g1A⁻¹ * (g1A * zA * g1A⁻¹)) : A6) : Perm (Fin 6)) * e *
    (((aA * zA * g1A)⁻¹ * (g1A * aA * g1A⁻¹ * (g1A * zA * g1A⁻¹)) : A6) : Perm (Fin 6))⁻¹ ∈
      e1List := by
  decide +kernel

theorem e1_n1 : ∀ e ∈ e1List, (n1A : Perm (Fin 6)) * e * (n1A : Perm (Fin 6))⁻¹ ∈ e1List := by
  decide +kernel

theorem e1_five : ((n1A * g1A : A6) : Perm (Fin 6)) ^ 5 = 1 ∧
    ((n1A * g1A : A6) : Perm (Fin 6)) ≠ 1 := by
  decide +kernel

theorem e2_c1 : ∀ e ∈ e2List, (((bA * zA * g2A)⁻¹ * (g2A * zA * g2A⁻¹) : A6) : Perm (Fin 6)) *
    e * (((bA * zA * g2A)⁻¹ * (g2A * zA * g2A⁻¹) : A6) : Perm (Fin 6))⁻¹ ∈ e2List := by
  decide +kernel

theorem e2_c2 : ∀ e ∈ e2List, (((bA * g2A)⁻¹ * (g2A * bA * g2A⁻¹) : A6) : Perm (Fin 6)) * e *
    (((bA * g2A)⁻¹ * (g2A * bA * g2A⁻¹) : A6) : Perm (Fin 6))⁻¹ ∈ e2List := by
  decide +kernel

theorem e2_c3 : ∀ e ∈ e2List,
    (((zA * g2A)⁻¹ * (g2A * bA * g2A⁻¹ * (g2A * zA * g2A⁻¹)) : A6) : Perm (Fin 6)) * e *
    (((zA * g2A)⁻¹ * (g2A * bA * g2A⁻¹ * (g2A * zA * g2A⁻¹)) : A6) : Perm (Fin 6))⁻¹ ∈
      e2List := by
  decide +kernel

theorem e2_five : ((zA * g2A : A6) : Perm (Fin 6)) ^ 5 = 1 ∧
    ((zA * g2A : A6) : Perm (Fin 6)) ≠ 1 := by
  decide +kernel

theorem orderOf_eq_five {x : A6} (h5 : (x : Perm (Fin 6)) ^ 5 = 1)
    (h1 : (x : Perm (Fin 6)) ≠ 1) : orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [orderOf_eq_prime_iff]
  exact ⟨Subtype.ext (by rw [Subgroup.coe_pow, h5]; rfl), fun h => h1 (congrArg Subtype.val h)⟩

theorem sup_g1_eq_top : N1 ⊔ Subgroup.zpowers g1A = ⊤ :=
  sup_zpowers_eq_top D0_le_N1 x0_mem_N1 orderOf_xA (mem_N1_of e1_n1)
    (orderOf_eq_five e1_five.1 e1_five.2)

theorem zA_mem_N2 : zA ∈ N2 :=
  mem_N2_of fun e he => d0_normalizes_e2 _ (e2_sub _ (by simp [e2List])) _ he

theorem sup_g2_eq_top : N2 ⊔ Subgroup.zpowers g2A = ⊤ :=
  sup_zpowers_eq_top D0_le_N2 y0_mem_N2 orderOf_yA zA_mem_N2
    (orderOf_eq_five e2_five.1 e2_five.2)

variable {W : Type*} [CommGroup W]

theorem const_of_rel_E1 (w : A6 → W) (hN : ∀ g : A6, ∀ n ∈ N1, w (g * n) = w g)
    (hrel : ∀ h g : A6, w g * w (h * zA * h⁻¹ * g) * w (h * aA * h⁻¹ * g) *
      w (h * aA * h⁻¹ * (h * zA * h⁻¹) * g) = 1) (g : A6) : w g = w 1 := by
  have hc : ∀ (x u v : A6), u⁻¹ * v ∈ N1 → w (x * v) = w (x * u) := by
    intro x u v huv
    have e : x * v = x * u * (u⁻¹ * v) := by group
    rw [e, hN _ _ huv]
  refine const_of_rel_gen w hN hrel (fun x => ?_) sup_g1_eq_top g
  rw [hc x (zA * g1A) _ (mem_N1_of e1_c1),
    hc x (aA * g1A) _ (mem_N1_of e1_c2),
    hc x (aA * zA * g1A) _ (mem_N1_of e1_c3)]

theorem const_of_rel_E2 (w : A6 → W) (hN : ∀ g : A6, ∀ n ∈ N2, w (g * n) = w g)
    (hrel : ∀ h g : A6, w g * w (h * zA * h⁻¹ * g) * w (h * bA * h⁻¹ * g) *
      w (h * bA * h⁻¹ * (h * zA * h⁻¹) * g) = 1) (g : A6) : w g = w 1 := by
  have hc : ∀ (x u v : A6), u⁻¹ * v ∈ N2 → w (x * v) = w (x * u) := by
    intro x u v huv
    have e : x * v = x * u * (u⁻¹ * v) := by group
    rw [e, hN _ _ huv]
  refine const_of_rel_gen w hN hrel (fun x => ?_) sup_g2_eq_top g
  rw [hc x (bA * zA * g2A) _ (mem_N2_of e2_c1),
    hc x (bA * g2A) _ (mem_N2_of e2_c2),
    hc x (zA * g2A) _ (mem_N2_of e2_c3)]
  rw [mul_comm (w (x * (bA * zA * g2A))) (w (x * (bA * g2A))), mul_comm _ (w (x * (zA * g2A))),
    ← mul_assoc, mul_comm (w (x * (zA * g2A))) (w (x * (bA * g2A)))]

end CFSG.Quasithin.H13.A6.Hat6
