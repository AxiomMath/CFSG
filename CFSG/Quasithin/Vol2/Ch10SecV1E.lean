module

public import CFSG.Quasithin.Vol2.Ch10SecV1D

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem zpowers_eq_one_or (hV : ∀ v : V, v ^ 2 = 1) {c z : V} (hz : z ∈ Subgroup.zpowers c) :
    z = 1 ∨ z = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hV]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem mem_sup_zpowers_iff (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup V} {c x : V} :
    x ∈ A ⊔ Subgroup.zpowers c ↔ x ∈ A ∨ x * c ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
    rcases zpowers_eq_one_or hV hz with rfl | rfl
    · left
      rwa [mul_one]
    · right
      rwa [mul_assoc, ← pow_two, hV, mul_one]
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have e : x = x * c * c := by rw [mul_assoc, ← pow_two, hV, mul_one]
      rw [e]
      exact Subgroup.mul_mem_sup h (Subgroup.mem_zpowers c)

theorem card_sup_zpowers [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup V} {c : V}
    (hc : c ∉ A) : Nat.card ↥(A ⊔ Subgroup.zpowers c) = 2 * Nat.card A := by
  have h := card_sup_mul_card_inf A (Subgroup.zpowers c)
  have hinf : A ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzA, hz⟩
    rcases zpowers_eq_one_or hV hz with rfl | rfl
    · exact Subgroup.one_mem _
    · exact (hc hzA).elim
  have hc1 : c ≠ 1 := fun h1 => hc (h1 ▸ A.one_mem)
  have hord : orderOf c = 2 := orderOf_eq_prime (hV c) hc1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord] at h
  rw [h, mul_comm]

theorem exists_card_eq_mul_pow [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K X : Subgroup V}
    (h : K ≤ X) : ∃ j : ℕ, Nat.card X = Nat.card K * 2 ^ j := by
  have hK := card_eq_two_pow hV K
  have hX := card_eq_two_pow hV X
  have hd := Subgroup.card_dvd_of_le h
  rw [hK, hX, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at hd
  exact ⟨rk X - rk K, by rw [hK, hX, ← pow_add, Nat.add_sub_cancel' hd]⟩

theorem card_eq_four_mul [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K X : Subgroup V} (h : K ≤ X)
    (h2 : 2 * Nat.card K < Nat.card X)
    (hsq : Nat.card X * Nat.card X ≤ 32 * (Nat.card K * Nat.card K)) :
    Nat.card X = 4 * Nat.card K := by
  obtain ⟨j, hj⟩ := exists_card_eq_mul_pow hV h
  have hK : 0 < Nat.card K := Nat.card_pos
  rw [hj] at h2 hsq ⊢
  have hj2 : 2 < 2 ^ j := by
    by_contra hc
    exact absurd h2 (not_lt.mpr (by nlinarith))
  have hj5 : 2 ^ j * 2 ^ j ≤ 32 := by
    have : Nat.card K * Nat.card K * (2 ^ j * 2 ^ j) ≤ Nat.card K * Nat.card K * 32 := by
      nlinarith
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  have hj' : j = 2 := by
    rcases Nat.lt_or_ge j 3 with hlt | hge
    · interval_cases j <;> simp_all
    · have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hge
      nlinarith
  rw [hj']
  ring

section Four

variable [Finite V] {G : Subgroup (MulAut V)} {W₂ W₁ : Subgroup V}

theorem two_mul_lt_of_lt (D : L3Data G W₂ W₁) {U C₀ K : Subgroup V}
    (hUinv : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) (hUU : U ≤ commSub U G) (hU8 : Nat.card U = 8 * Nat.card C₀)
    (hKU : K ≤ U) (hKF : K ≤ fixV G) (hlt : Nat.card K < Nat.card C₀) :
    2 * Nat.card K < Nat.card ↥(U.map (commHom (D.rho L3.x12)) ⊔ K) := by
  by_contra h
  have hb := comm_bound D hUinv hKU hKF (not_lt.mp h)
  have hle := Subgroup.card_le_of_le (hUU.trans (le_sup_left : commSub U G ≤ commSub U G ⊔ K))
  omega

theorem false_of_four_le_aux (hV : ∀ v : V, v ^ 2 = 1) (D : L3Data G W₂ W₁) {U C₀ : Subgroup V}
    (hUinv : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) (hUU : U ≤ commSub U G) (hC₀U : C₀ ≤ U)
    (hC₀F : C₀ ≤ fixV G) (hU8 : Nat.card U = 8 * Nat.card C₀) (hcard : 4 ≤ Nat.card C₀) :
    False := by
  have htU : ∀ u ∈ U, D.rho L3.x12 u ∈ U := hUinv _ (D.rho_mem _)
  obtain ⟨C', hC'C₀, hC'card⟩ : ∃ C' : Subgroup V, C' ≤ C₀ ∧ Nat.card C₀ = 4 * Nat.card C' := by
    have h2 := card_eq_two_pow hV C₀
    have hr : 2 ≤ rk C₀ := by
      by_contra hr
      have : 2 ^ rk C₀ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨H', hH'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C₀) 2 (n := rk C₀ - 2)
      (by rw [h2]; exact Nat.pow_dvd_pow 2 (Nat.sub_le _ 2))
    refine ⟨H'.map C₀.subtype, Subgroup.map_subtype_le H', ?_⟩
    rw [Subgroup.card_map_of_injective C₀.subtype_injective, hH', h2]
    conv_lhs => rw [show rk C₀ = (rk C₀ - 2) + 2 by omega, pow_add]
    ring
  have hC'U : C' ≤ U := hC'C₀.trans hC₀U
  have hC'F : C' ≤ fixV G := hC'C₀.trans hC₀F
  have hC'pos : 0 < Nat.card C' := Nat.card_pos
  obtain ⟨X, hX⟩ : ∃ X, X = U.map (commHom (D.rho L3.x12)) ⊔ C' := ⟨_, rfl⟩
  have hXcard : Nat.card X = 4 * Nat.card C' := by
    rw [hX]
    refine card_eq_four_mul hV le_sup_right
      (two_mul_lt_of_lt D hUinv hUU hU8 hC'U hC'F (by omega)) ?_
    have := sq_bound D hV hUinv hC'U hC'F
    rw [pow_two, hU8, hC'card] at this
    linarith
  have hXC₀ : X ⊓ C₀ ≤ C' := by
    rintro c ⟨hcX, hcC₀⟩
    by_contra hc
    have hH : Nat.card ↥(C' ⊔ Subgroup.zpowers c) = 2 * Nat.card C' := card_sup_zpowers hV hc
    have hHC₀ : C' ⊔ Subgroup.zpowers c ≤ C₀ := sup_le hC'C₀ (Subgroup.zpowers_le.mpr hcC₀)
    have hXH : Nat.card ↥(U.map (commHom (D.rho L3.x12)) ⊔ (C' ⊔ Subgroup.zpowers c)) =
        4 * Nat.card ↥(C' ⊔ Subgroup.zpowers c) := by
      refine card_eq_four_mul hV le_sup_right (two_mul_lt_of_lt D hUinv hUU hU8
        (hHC₀.trans hC₀U) (hHC₀.trans hC₀F) (by omega)) ?_
      have := sq_bound D hV hUinv (hHC₀.trans hC₀U) (hHC₀.trans hC₀F)
      rw [pow_two, hU8, hC'card, hH] at this
      rw [hH]
      nlinarith
    have hsup : X ⊔ (C' ⊔ Subgroup.zpowers c) =
        U.map (commHom (D.rho L3.x12)) ⊔ (C' ⊔ Subgroup.zpowers c) := by
      rw [hX, sup_assoc, sup_eq_right.mpr (le_sup_left : C' ≤ C' ⊔ Subgroup.zpowers c)]
    have hinf := card_sup_mul_card_inf X (C' ⊔ Subgroup.zpowers c)
    rw [hsup, hXH, hXcard, hH] at hinf
    have hcard' : Nat.card ↥(X ⊓ (C' ⊔ Subgroup.zpowers c)) = Nat.card C' := by
      have : (8 * Nat.card C') * Nat.card ↥(X ⊓ (C' ⊔ Subgroup.zpowers c)) =
          (8 * Nat.card C') * Nat.card C' := by linarith
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have hC'X : C' ≤ X := hX ▸ le_sup_right
    have heq : C' = X ⊓ (C' ⊔ Subgroup.zpowers c) :=
      Subgroup.eq_of_le_of_card_ge (le_inf hC'X le_sup_left) hcard'.le
    have hmem : c ∈ X ⊓ (C' ⊔ Subgroup.zpowers c) :=
      ⟨hcX, Subgroup.mem_sup_right (Subgroup.mem_zpowers c)⟩
    rw [← heq] at hmem
    exact hc hmem
  have hC'X : C' ≤ X := hX ▸ le_sup_right
  have hXC₀' : X ⊓ C₀ = C' := le_antisymm hXC₀ (le_inf hC'X hC'C₀)
  have h16 : Nat.card ↥(X ⊔ C₀) = 16 * Nat.card C' := by
    have h := card_sup_mul_card_inf X C₀
    rw [hXC₀', hXcard, hC'card] at h
    have : Nat.card ↥(X ⊔ C₀) * Nat.card C' = (16 * Nat.card C') * Nat.card C' := by linarith
    exact Nat.eq_of_mul_eq_mul_right hC'pos this
  have hle : X ⊔ C₀ ≤ fixRel (D.rho L3.x12) U C' := by
    rw [hX]
    refine sup_le (map_sup_le_fixRel hV (rho_invol D L3.x12_invol) htU hC'U
      (fun _ hk => hC'F hk _ (D.rho_mem _))) ?_
    intro c hc
    refine ⟨hC₀U hc, ?_⟩
    change D.rho L3.x12 c * c⁻¹ ∈ C'
    rw [hC₀F hc _ (D.rho_mem _), mul_inv_cancel]
    exact C'.one_mem
  have hfix := card_sup_mul_card_fixRel (D.rho L3.x12) U C'
  rw [← hX, hXcard, hU8, hC'card] at hfix
  have h8 : Nat.card ↥(fixRel (D.rho L3.x12) U C') = 8 * Nat.card C' := by
    have : (4 * Nat.card C') * Nat.card ↥(fixRel (D.rho L3.x12) U C') =
        (4 * Nat.card C') * (8 * Nat.card C') := by linarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have := Subgroup.card_le_of_le hle
  omega

end Four

end CFSG.Quasithin.Vol2.Ch10.V1C
