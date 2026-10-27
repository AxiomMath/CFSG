module

public import CFSG.Sporadic.HN.CoprimeSimple

public section

namespace CFSG.Sporadic.Ly

open Subgroup CFSG.Sporadic.HN

variable {G : Type*} [Group G] [Finite G]

theorem eq_top_of_conjProd_mem_coprime {a b g : G} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hgen : closure {a, b} = ⊤) (ha : a ^ m = 1) (hb : b ^ n = 1) {N : Subgroup G} [N.Normal]
    (hx : a * (g⁻¹ * b * g) ∈ N) : N = ⊤ := by
  let f := QuotientGroup.mk' N
  have hx' : f a * ((f g)⁻¹ * f b * f g) = 1 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).2 hx
  have ha' : f a ^ m = 1 := by rw [← map_pow, ha, map_one]
  have hb' : f b ^ n = 1 := by rw [← map_pow, hb, map_one]
  have hA : f a = MulAut.conj (f g)⁻¹ (f b)⁻¹ := by
    rw [MulAut.conj_apply, inv_inv]
    calc f a = f a * ((f g)⁻¹ * f b * f g) * ((f g)⁻¹ * f b * f g)⁻¹ := by group
      _ = (f g)⁻¹ * (f b)⁻¹ * f g := by rw [hx']; group
  have hAn : f a ^ n = 1 := by rw [hA, ← map_pow, inv_pow, hb', inv_one, map_one]
  have hA1 : f a = 1 :=
    orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hmn (orderOf_dvd_of_pow_eq_one ha')
      (orderOf_dvd_of_pow_eq_one hAn))
  have hB1 : f b = 1 := by
    rw [MulAut.conj_apply, inv_inv] at hA
    have e : f b = f g * ((f g)⁻¹ * (f b)⁻¹ * f g)⁻¹ * (f g)⁻¹ := by group
    rw [e, ← hA, hA1]
    group
  have haN : a ∈ N := (QuotientGroup.eq_one_iff a).1 hA1
  have hbN : b ∈ N := (QuotientGroup.eq_one_iff b).1 hB1
  rw [eq_top_iff, ← hgen, closure_le]
  rintro y (rfl | rfl)
  · exact haN
  · exact hbN

theorem isSimpleGroup_of_conjProd_coprime {a b g : G} {m n q : ℕ} (hmn : Nat.Coprime m n)
    (hq : q.Prime) (hgen : closure {a, b} = ⊤) (ha : a ^ m = 1) (hb : b ^ n = 1)
    (hx : orderOf (a * (g⁻¹ * b * g)) = q) (hq2 : ¬ q ^ 2 ∣ Nat.card G) (hZ : center G = ⊥)
    (hGL : ∀ p e : ℕ, p.Prime → p ≠ q → p ^ e ∣ Nat.card G →
      ∀ r ≤ e, ¬ q ∣ Nat.card (GL (Fin r) (ZMod p))) :
    IsSimpleGroup G := by
  have : Fact q.Prime := ⟨hq⟩
  set x := a * (g⁻¹ * b * g)
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx
    exact hq.one_lt.ne hx
  have : Nontrivial G := nontrivial_of_ne x 1 hx1
  refine ⟨fun N hN => ?_⟩
  by_cases hNq : q ∣ Nat.card N
  · exact Or.inr (eq_top_of_conjProd_mem_coprime hmn hgen ha hb (mem_of_dvd_card hx hq2 hNq))
  · left
    have hxC : x ∈ centralizer (N : Set G) := by
      rw [mem_centralizer_iff]
      intro n hn
      have := le_centralizer_of_not_dvd_card hx hGL hNq hn
      rw [mem_centralizer_singleton_iff] at this
      exact this
    have hCN : centralizer (N : Set G) = ⊤ := eq_top_of_conjProd_mem_coprime hmn hgen ha hb hxC
    rw [eq_bot_iff, ← hZ]
    intro n hn
    rw [mem_center_iff]
    intro y
    have := (mem_centralizer_iff.1 (hCN ▸ mem_top y : y ∈ centralizer (N : Set G))) n hn
    exact this.symm

theorem pow_le_of_dvd_ly {p e m : ℕ} (hp : 1 < p) (hd : p ^ e ∣ 51765179004000000)
    (hm : ¬ p ^ (m + 1) ∣ 51765179004000000) : e ≤ m := by
  by_contra h
  exact hm ((pow_dvd_pow p (by omega)).trans hd)

theorem ly_GL_condition : ∀ p e : ℕ, p.Prime → p ≠ 67 → p ^ e ∣ 51765179004000000 →
    ∀ r ≤ e, ¬ 67 ∣ Nat.card (GL (Fin r) (ZMod p)) := by
  intro p e hp hpq hd r hr
  have : Fact p.Prime := ⟨hp⟩
  refine not_dvd_card_GL (by norm_num) (Ne.symm hpq) fun k hk1 hkr => ?_
  have hpN : p ∣ 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 :=
    (dvd_pow_self p (by omega : e ≠ 0)).trans hd
  have hpl : ∀ l : ℕ, l.Prime → p ∣ l → p = l := fun l hl h => (Nat.prime_dvd_prime_iff_eq hp hl).1 h
  have hk : ∀ m : ℕ, ¬ p ^ (m + 1) ∣ 51765179004000000 → k ≤ m := fun m hm =>
    le_trans hkr <| le_trans hr <| pow_le_of_dvd_ly hp.one_lt hd hm
  rcases (Nat.Prime.dvd_mul hp).1 hpN with h | h67
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h37
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h31
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h11
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h7
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
            · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
              · obtain rfl := hpl 2 (by norm_num) (hp.dvd_of_dvd_pow h2)
                have : k ≤ 8 := hk 8 (by norm_num)
                interval_cases k <;> norm_num
              · obtain rfl := hpl 3 (by norm_num) (hp.dvd_of_dvd_pow h3)
                have : k ≤ 7 := hk 7 (by norm_num)
                interval_cases k <;> norm_num
            · obtain rfl := hpl 5 (by norm_num) (hp.dvd_of_dvd_pow h5)
              have : k ≤ 6 := hk 6 (by norm_num)
              interval_cases k <;> norm_num
          · obtain rfl := hpl 7 (by norm_num) h7
            have : k ≤ 1 := hk 1 (by norm_num)
            interval_cases k <;> norm_num
        · obtain rfl := hpl 11 (by norm_num) h11
          have : k ≤ 1 := hk 1 (by norm_num)
          interval_cases k <;> norm_num
      · obtain rfl := hpl 31 (by norm_num) h31
        have : k ≤ 1 := hk 1 (by norm_num)
        interval_cases k <;> norm_num
    · obtain rfl := hpl 37 (by norm_num) h37
      have : k ≤ 1 := hk 1 (by norm_num)
      interval_cases k <;> norm_num
  · exact absurd (hpl 67 (by norm_num) h67) hpq

end CFSG.Sporadic.Ly
