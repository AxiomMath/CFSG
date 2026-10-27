module

public import CFSG.Quasithin.Vol2.Ch11SecO7x
public import CFSG.Quasithin.Vol2.Ch11SecO7w

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

@[expose] def List11Concl {G : Type} [Group G] (L : Subgroup G) : Prop :=
  IsSporadic .M23 ↥L ∨ IsSporadic .J4 ↥L ∨
    (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (IsPSL 2 p 2 ↥L ∨ IsPSL 3 p 1 ↥L ∨ IsSL3 p ↥L ∨
      IsPSU 3 p 1 ↥L ∨ IsSU3 p ↥L))

variable {Y : Type} [Group Y] [Finite Y] {B L : Subgroup Y} {X : Type} [Group X]

theorem five_le_of_prime {r : ℕ} (hr : r.Prime) (h : 3 < r) : 5 ≤ r := by
  by_contra h'
  obtain rfl : r = 4 := by omega
  norm_num at hr

theorem a312List11_c10 (e : ModO2 B ≃* X) (hXq : CFSG.IsQuasisimple X)
    (hXZ : Nat.card (Subgroup.center X) ∣ 3) (h : A312C10 B L) : False := by
  obtain ⟨r, hr, hr3, ⟨V, hVn, ⟨fV⟩, ⟨f⟩⟩, -⟩ := h
  have : Fact r.Prime := ⟨hr⟩
  have hr5 := five_le_of_prime hr hr3
  obtain ⟨c, hc3, hc⟩ := card_of_surj_sl2 e hXq hXZ hr5
    (f.toMonoidHom.comp (QuotientGroup.mk' V)) (f.surjective.comp (QuotientGroup.mk'_surjective V))
  obtain ⟨b, hb⟩ := card_modO2_mul e
  have hV : Nat.card V = r ^ 2 := by
    rw [Nat.card_congr fV.toEquiv]
    show Nat.card (Fin 2 → ZMod r) = r ^ 2
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hBV : Nat.card (↥B ⧸ V) = r * (r ^ 2 - 1) := by
    rw [Nat.card_congr f.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
  have hBc : Nat.card ↥B = r * (r ^ 2 - 1) * r ^ 2 := by
    rw [V.card_eq_card_quotient_mul_card_subgroup, hBV, hV]
  have hr2 : 25 ≤ r ^ 2 := by nlinarith
  have hpos : 0 < r * (r ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  have h1 : r * (r ^ 2 - 1) * (c * 2 ^ b) = r * (r ^ 2 - 1) * (2 * r ^ 2) := by
    calc r * (r ^ 2 - 1) * (c * 2 ^ b) = c * (r * (r ^ 2 - 1)) * 2 ^ b := by ring
      _ = Nat.card X * 2 * 2 ^ b := by rw [hc]
      _ = Nat.card ↥B * 2 := by rw [hb]; ring
      _ = r * (r ^ 2 - 1) * (2 * r ^ 2) := by rw [hBc]; ring
  have h2 : c * 2 ^ b = 2 * r ^ 2 := Nat.eq_of_mul_eq_mul_left hpos h1
  have h3 : r ^ 2 ∣ c := by
    have : r ^ 2 ∣ c * 2 ^ b := ⟨2, by rw [h2]; ring⟩
    exact (Nat.Coprime.pow 2 b ((Nat.coprime_primes hr Nat.prime_two).mpr
      (by omega))).dvd_of_dvd_mul_right this
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hc3 (by norm_num)
  have h4 := Nat.le_of_dvd hc0 h3
  have h5 := Nat.le_of_dvd (by norm_num) hc3
  omega


theorem a312List11_c9 {n : ℕ} (e : ModO2 B ≃* X) (hIn : InLists X n)
    (hXq : CFSG.IsQuasisimple X) (hXZ : Nat.card (Subgroup.center X) ∣ 3) (h : A312C9 B L) :
    n = 2 ∧ List11Concl L := by
  have : Finite X := Finite.of_equiv _ e.toEquiv
  have hB : ∀ N, Nat.card ↥B = N → 0 < N → N ≤ 1080 → ¬ 660 ∣ N → False :=
    fun N hN h2 h3 h4 => lists_not_dvd hIn (hN ▸ card_dvd_B e) h2 h3 h4
  rcases h with ⟨s, r, hr, hr3, ⟨f⟩, hL⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · have : Fact r.Prime := ⟨hr⟩
    have hr5 := five_le_of_prime hr hr3
    obtain ⟨c, hc3, hc⟩ := card_of_surj_sl2 e hXq hXZ hr5 f.toMonoidHom f.surjective
    obtain ⟨b, hb⟩ := card_modO2_mul e
    have hBc : Nat.card ↥B = r * (r ^ 2 - 1) := by
      rw [Nat.card_congr f.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
    have hX0 : 0 < Nat.card X := Nat.card_pos
    have h1 : Nat.card X * 2 = Nat.card X * (c * 2 ^ b) := by rw [hc, ← hBc, hb]; ring
    have h2 : 2 = c * 2 ^ b := Nat.eq_of_mul_eq_mul_left hX0 h1
    have hc1 : c = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp ⟨2 ^ b, h2⟩ with h | h
      · exact h
      · rw [h] at hc3
        norm_num at hc3
    rw [hc1, one_mul] at hc
    obtain ⟨hn2, h11⟩ := psl2_case hIn hr hr5 hc
    refine ⟨hn2, Or.inr (Or.inr ⟨r, hr, h11, ?_⟩)⟩
    cases s
    · rcases hL with hL | hL
      · exact Or.inr (Or.inr (Or.inr (Or.inl hL)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hL)))
    · rcases hL with hL | hL
      · exact Or.inr (Or.inl hL)
      · exact Or.inr (Or.inr (Or.inl hL))
  · exact (hB 360 (card_of_isAlt6 h1) (by norm_num) (by norm_num) (by norm_num)).elim
  · exact (hB 1080 (card_of_isHatAlt6 h1) (by norm_num) (by norm_num) (by norm_num)).elim

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
