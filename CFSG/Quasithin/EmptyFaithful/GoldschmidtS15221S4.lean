module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.S15221

open Equiv Equiv.Perm CFSG.Quasithin

structure S4Like (Γ : Type*) [Group Γ] : Prop where
  exists_V : ∃ V : Subgroup Γ, V.Normal ∧ IsPGroup 2 V ∧ V ≤ oTwoUpper (⊤ : Subgroup Γ) ∧
    V.relIndex (oTwoUpper (⊤ : Subgroup Γ)) = 3 ∧
    (∀ N : Subgroup Γ, N.Normal → IsPGroup 2 N → N ≤ V) ∧
    (∀ N : Subgroup Γ, N ≤ oTwoUpper (⊤ : Subgroup Γ) → IsPGroup 2 N → N ≤ V) ∧
    (∀ a b : Γ, a ∉ V → (∃ k : ℕ, a ^ 2 ^ k = 1) → b ∈ oTwoUpper (⊤ : Subgroup Γ) → b ∉ V →
      a * b * a⁻¹ * b⁻¹ ∉ V) ∧
    (∃ a : Γ, a ∉ V ∧ ∃ k : ℕ, a ^ 2 ^ k = 1) ∧ Nat.card V = 4 ∧
    (∀ P : Subgroup Γ, IsPGroup 2 P → ¬ 2 ∣ P.index → 8 ≤ Nat.card P)

@[expose] def KleinP (x : Perm (Fin 4)) : Prop := x = 1 ∨ ((∀ i, x i ≠ i) ∧ ∀ i, x (x i) = i)

instance (x : Perm (Fin 4)) : Decidable (KleinP x) := by unfold KleinP; infer_instance

theorem kleinP_mul : ∀ x y : Perm (Fin 4), KleinP x → KleinP y → KleinP (x * y) := by
  decide +kernel

theorem kleinP_inv : ∀ x : Perm (Fin 4), KleinP x → KleinP x⁻¹ := by decide +kernel

theorem kleinP_one : KleinP (1 : Perm (Fin 4)) := by decide +kernel

theorem kleinP_conj : ∀ x g : Perm (Fin 4), KleinP x → KleinP (g * x * g⁻¹) := by decide +kernel

theorem kleinP_sq : ∀ x : Perm (Fin 4), KleinP x → x ^ 2 = 1 := by decide +kernel

theorem kleinP_card : (Finset.univ.filter fun x : Perm (Fin 4) => KleinP x).card = 4 := by
  decide +kernel

theorem kleinP_sign : ∀ x : Perm (Fin 4), KleinP x → sign x = 1 := by decide +kernel

theorem alt_not_klein : ∀ x : Perm (Fin 4), sign x = 1 → ¬ KleinP x → x ^ 3 = 1 ∧ x ≠ 1 := by
  decide +kernel

theorem key_comm : ∀ x : Perm (Fin 4), ¬ KleinP x → x ^ 8 = 1 →
    ∃ g : Perm (Fin 4), (x * g * x⁻¹ * g⁻¹) ^ 3 = 1 ∧ x * g * x⁻¹ * g⁻¹ ≠ 1 := by decide +kernel

theorem comm_fact : ∀ a b : Perm (Fin 4), ¬ KleinP a → a ^ 8 = 1 → sign b = 1 → ¬ KleinP b →
    ¬ KleinP (a * b * a⁻¹ * b⁻¹) := by decide +kernel

@[expose] def kleinFour : Subgroup (Perm (Fin 4)) where
  carrier := {x | KleinP x}
  mul_mem' := fun {x y} hx hy => kleinP_mul x y hx hy
  one_mem' := kleinP_one
  inv_mem' := fun {x} hx => kleinP_inv x hx

theorem oTwoUpper_top_perm_four :
    oTwoUpper (⊤ : Subgroup (Perm (Fin 4))) = alternatingGroup (Fin 4) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (sign x) with h | h
    · exact h
    · exfalso
      have h1 : sign x ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [h, Odd.neg_one_pow hx.2] at h1
      exact absurd h1 (by decide)
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    refine Subgroup.closure_mono fun x hx => ⟨Subgroup.mem_top x, ?_⟩
    rw [hx.orderOf]
    exact ⟨1, rfl⟩

theorem pow_eight_of_two_pow {x : Perm (Fin 4)} (h : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ^ 8 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, hm, hmx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf x ∣ 24 := by
    have := orderOf_dvd_card (G := Perm (Fin 4)) (x := x)
    rw [Fintype.card_perm, Fintype.card_fin] at this
    simpa [Nat.factorial] using this
  have hm3 : m ≤ 3 := by
    by_contra hlt
    have : 2 ^ 4 ∣ 2 ^ m := pow_dvd_pow 2 (by omega)
    have h3 : 2 ^ 4 ∣ 24 := this.trans (hmx ▸ h2)
    omega
  have : orderOf x ∣ 8 := by
    rw [hmx]
    exact (pow_dvd_pow 2 hm3 : 2 ^ m ∣ 2 ^ 3)
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem s4Like_perm_fin4 : S4Like (Perm (Fin 4)) := by
  have hA := oTwoUpper_top_perm_four
  have hVA : kleinFour ≤ oTwoUpper (⊤ : Subgroup (Perm (Fin 4))) := by
    rw [hA]
    exact fun x hx => Equiv.Perm.mem_alternatingGroup.mpr (kleinP_sign x hx)
  have hV2 : IsPGroup 2 kleinFour := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    exact kleinP_sq g.1 g.2
  have hcardV : Nat.card kleinFour = 4 := by
    show Nat.card {x : Perm (Fin 4) // KleinP x} = 4
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, kleinP_card]
  have hcardA : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hnotpow : ∀ x : Perm (Fin 4), (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 3 = 1 → x = 1 := by
    intro x ⟨k, hk⟩ h3
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have : orderOf x ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd h1 h2
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
    rw [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  refine ⟨⟨kleinFour, ⟨fun x hx g => kleinP_conj x g hx⟩, hV2, hVA, ?_, ?_, ?_, ?_, ?_, hcardV, ?_⟩⟩
  · rw [hA]
    have h1 := Subgroup.card_mul_index (H := kleinFour.subgroupOf (alternatingGroup (Fin 4)))
    have h2 : Nat.card (kleinFour.subgroupOf (alternatingGroup (Fin 4))) = 4 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hA ▸ hVA)).toEquiv).trans hcardV
    rw [h2, hcardA] at h1
    show (kleinFour.subgroupOf (alternatingGroup (Fin 4))).index = 3
    omega
  · intro N hN hN2 x hx
    by_contra hxV
    have hx8 : x ^ 8 = 1 := pow_eight_of_two_pow (by
      obtain ⟨k, hk⟩ := hN2 ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
    obtain ⟨g, hg3, hg1⟩ := key_comm x hxV hx8
    have hcN : x * g * x⁻¹ * g⁻¹ ∈ N := by
      have : g * x⁻¹ * g⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hx) g
      have h2 := N.mul_mem hx this
      simpa [mul_assoc] using h2
    obtain ⟨k, hk⟩ := hN2 ⟨_, hcN⟩
    exact hg1 (hnotpow _ ⟨k, by simpa using congrArg Subtype.val hk⟩ hg3)
  · intro N hNA hN2 x hx
    by_contra hxV
    have hxA : sign x = 1 := Equiv.Perm.mem_alternatingGroup.mp (hA ▸ hNA hx)
    obtain ⟨h3, h1⟩ := alt_not_klein x hxA hxV
    obtain ⟨k, hk⟩ := hN2 ⟨x, hx⟩
    exact h1 (hnotpow _ ⟨k, by simpa using congrArg Subtype.val hk⟩ h3)
  · intro a b ha ha2 hb hbV
    have hbA : sign b = 1 := Equiv.Perm.mem_alternatingGroup.mp (hA ▸ hb)
    exact comm_fact a b ha (pow_eight_of_two_pow ha2) hbA hbV
  · refine ⟨swap 0 1, ?_, 1, ?_⟩
    · show ¬ KleinP (swap 0 1)
      decide +kernel
    · show swap (0 : Fin 4) 1 ^ 2 ^ 1 = 1
      decide +kernel
  · intro P hP2 hPi
    have h1 := Subgroup.card_mul_index (H := P)
    have hc24 : Nat.card (Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have h24 : Nat.card P * P.index = 24 := hc24 ▸ h1
    have hcop : Nat.Coprime 8 P.index := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hPi)
    have : 8 ∣ Nat.card P := hcop.dvd_of_dvd_mul_right ⟨3, by omega⟩
    exact Nat.le_of_dvd Nat.card_pos this

end CFSG.Quasithin.S15221
