module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Sound
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38AbsB
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38AbsC

public section

open CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

variable {H : Type*} [Group H] [Finite H] {Ω : Type*} [Finite Ω] [MulAction H Ω]

theorem prime_dvd_card_cases {r : ℕ} (hr : r.Prime) (h : r ∣ 99283968) :
    r = 2 ∨ r = 3 ∨ r = 7 ∨ r = 19 := by
  have hf : (99283968 : ℕ) = 2 ^ 10 * 3 ^ 6 * 7 * 19 := by norm_num
  rw [hf] at h
  rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3)
        exact Or.inl this
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h3)
        exact Or.inr (Or.inl this)
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 7)).1 h2
      exact Or.inr (Or.inr (Or.inl this))
  · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 19)).1 h1
    exact Or.inr (Or.inr (Or.inr this))

theorem k0_abstract
    (hΩ : Nat.card Ω = 513) (hH : Nat.card H = 99283968)
    (h2 : ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ g : H, g • a = a' ∧ g • b = b')
    {ω0 : Ω} {y9 : H} (hy9 : orderOf y9 = 9) (hy9f : y9 • ω0 = ω0)
    {x7 : H} (hx7 : orderOf x7 = 7) (hx7f : Nat.card {p : Ω // x7 • p = p} = 2)
    {ω1 ω2 : Ω} (hne : ω1 ≠ ω2) {σ : H} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hσf1 : σ • ω1 = ω1) (hσf2 : σ • ω2 = ω2)
    (hC : Nat.card (Subgroup.centralizer ({σ} : Set H)) = 3024)
    {y' : H} (hyC : y' ∈ Subgroup.centralizer ({σ} : Set H)) (hy' : orderOf y' = 9)
    {x19 : H} (hx19 : orderOf x19 = 19)
    (hC19 : Nat.card (Subgroup.centralizer ({x19} : Set H)) ≤ 57) :
    ∀ E Y : Subgroup H, IsElemAbelian 3 E → Nat.card E = 27 → ¬ 3 ∣ Nat.card Y →
      E ≤ Subgroup.normalizer (Y : Set H) → Y = ⊥ := by
  intro E Y hE hE27 hY3 hEY
  by_contra hYbot
  have htrans : MulAction.IsPretransitive H Ω :=
    isPretransitive_of_two_transitive (by omega) h2
  have hA : ∀ (E : Subgroup H), IsElemAbelian 3 E → Nat.card E = 27 → ∀ ω : Ω,
      ¬ ∀ e ∈ E, e • ω = ω := fun E hE hE27 ω =>
    no_E27_fixes_point hΩ hH htrans hy9 hy9f hE hE27 ω
  obtain ⟨r, hr, hr3, V, hVne, hVab, hVnorm⟩ :=
    exists_elemAbelian_normalized hE.2 hY3 hYbot hEY
  haveI : Fact r.Prime := ⟨hr⟩
  have hrdvd : r ∣ 99283968 := by
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hVne (Subgroup.eq_bot_iff_forall V |>.2 hcon)
    have hvr : (⟨v, hv⟩ : V) ^ r = 1 := Subtype.ext (by simpa using hVab.2 v hv)
    have hv1' : (⟨v, hv⟩ : V) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
    have hord : orderOf (⟨v, hv⟩ : V) = r :=
      orderOf_eq_prime hvr hv1'
    have h1 : orderOf (⟨v, hv⟩ : V) ∣ Nat.card V := orderOf_dvd_natCard _
    have h3 : Nat.card V ∣ Nat.card H := Subgroup.card_subgroup_dvd_card V
    rw [hord] at h1
    rw [hH] at h3
    exact h1.trans h3
  rcases prime_dvd_card_cases hr hrdvd with rfl | rfl | rfl | rfl
  · exact no_E27_normalizes_two hΩ hH h2 hA hne hσ2 hσ1 hσf1 hσf2 hC hyC hy' hVab hVne hE hE27 hVnorm
  · exact hr3 rfl
  · exact no_E27_normalizes_seven hH hA hx7 hx7f hVab hVne hE hE27 hVnorm
  · exact no_E27_normalizes_nineteen hH hx19 hC19 hVab hVne hE hE27 hVnorm

end CFSG.RankThree.PartTwo.Sec4.Item434U38
