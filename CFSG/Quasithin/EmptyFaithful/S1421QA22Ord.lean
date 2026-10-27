module

public import CFSG.Quasithin.EmptyFaithful.R3c7Ord
public import CFSG.Quasithin.EmptyFaithful.S146yB1Res

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Ch1 (IsFermatOrMersennePrime)
open CFSG.Quasithin.R3c7

@[expose] def Lemma115OrdClass : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → Lemma115Type K →
    OrdClass (Nat.card (K ⧸ Subgroup.center K))

theorem padicValNat_175560 : padicValNat 2 175560 = 3 :=
  CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 21945) (a := 3) odd_one
    (by decide) (by norm_num)

theorem not_ordClass_175560 : ¬ OrdClass 175560 := by
  intro hc
  cases hc with
  | @big2 _ a b ha hb h1 h2 =>
    rw [padicValNat_175560] at ha
    subst ha
    have : 2 ^ b ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  | l3two h => omega
  | @l2two f _ hf h =>
    have h3 := padicValNat_l2two (by omega) h
    rw [padicValNat_175560] at h3
    subst h3
    omega
  | @l2fm p _ hp h =>
    have hp2 : 2 ≤ p := hp.1.two_le
    have hlt : p < 72 := by
      by_contra hge
      push Not at hge
      have h1 : 72 ≤ p := hge
      have h3 : 72 * (72 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
        Nat.mul_le_mul h1 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 2) 1)
      omega
    interval_cases p <;> omega
  | small h => omega
  | spor h => rcases h with h | h | h | h | h | h | h | h | h | h <;> omega

theorem eq_three_or_five_of_fm {p : ℕ} (hp : IsFermatOrMersennePrime p)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) : p = 3 ∨ p = 5 := by
  obtain ⟨hpp, ⟨k, hk⟩ | ⟨k, hk2, hk⟩⟩ := hp
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · left; simpa using hk
      · right; simpa using hk
    · exfalso
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      have h8d : 8 ∣ 2 ^ 2 ^ k := by
        have := pow_dvd_pow 2 (by omega : 3 ≤ 2 ^ k)
        simpa using this
      generalize 2 ^ 2 ^ k = x at hk h8d
      omega
  · rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have : k = 2 := by omega
      subst this
      left; simpa using hk
    · exfalso
      have h8d : 8 ∣ 2 ^ k := by
        have := pow_dvd_pow 2 hk3
        simpa using this
      have hpos : 0 < 2 ^ k := by positivity
      generalize 2 ^ k = x at hk h8d hpos
      omega

theorem R3c7.OrdClass.false_of_l2p_three {N p : ℕ} (hc : OrdClass N) (hp : p.Prime)
    (h5 : p % 5 = 1 ∨ p % 5 = 4) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (h : N * 2 = p * (p ^ 2 - 1)) : False := by
  have hp2 : 2 ≤ p := hp.two_le
  have hmod16 : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
  have hsq : (p ^ 2) % 16 = 9 := by
    rcases hmod16 with h1 | h1 | h1 | h1 <;> simp [Nat.pow_mod, h1]
  have hq : (p ^ 2 - 1) % 16 = 8 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hN16 : (N * 2) % 16 = 8 := by
    rw [h, Nat.mul_mod, hq]
    rcases hmod16 with h1 | h1 | h1 | h1 <;> simp [h1]
  have hN8 : N % 8 = 4 := by omega
  obtain ⟨t, ht⟩ : ∃ t, N = 4 * (2 * t + 1) := ⟨N / 8, by omega⟩
  have hv : padicValNat 2 N = 2 :=
    CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 2 * t + 1) (a := 2) odd_one
      (odd_two_mul_add_one t) (by rw [ht]; ring)
  have hp5 : p < 6 → False := by
    intro hlt
    interval_cases p <;> omega
  have hsmall : ∀ q : ℕ, 6 ≤ q → 120 < q * (q ^ 2 - 1) := by
    intro q hq6
    have h1 : 6 * (6 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq6 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq6 2) 1)
    omega
  cases hc with
  | @big2 _ a b ha hb h1 h2 =>
    rw [hv] at ha
    subst ha
    have : 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hN : N < 16 := by omega
    have : p * (p ^ 2 - 1) < 32 := by omega
    by_contra _
    exact hp5 (by by_contra hge; push Not at hge; have := hsmall p hge; omega)
  | l3two h' => omega
  | @l2two f _ hf h' =>
    rcases Nat.lt_or_ge f 3 with hf3 | hf3
    · have : f = 2 := by omega
      subst this
      have hN : N = 60 := by rw [h']; norm_num
      have : p * (p ^ 2 - 1) = 120 := by omega
      exact hp5 (by by_contra hge; push Not at hge; have := hsmall p hge; omega)
    · have h8d : 8 ∣ N := by
        rw [h']
        have h8f : 8 ∣ 2 ^ f := by
          have := pow_dvd_pow 2 hf3
          simpa using this
        exact Dvd.dvd.mul_right h8f _
      omega
  | @l2fm p' _ hp' h' =>
    have hpp' : p = p' := eq_of_l2_orders (by omega) hp'.1.one_lt.le h h'
    subst hpp'
    rcases eq_three_or_five_of_fm hp' h8 with h3 | h3 <;> omega
  | small h' => omega
  | spor h' => rcases h' with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;> omega

theorem not_ordClass_372000 : ¬ OrdClass 372000 := fun hc =>
  hc.false_of_oddLike (oddLike_of_sl3 (p := 5) (N := 372000) (g := 1) (by decide) le_rfl
    (by norm_num) (by norm_num))

theorem not_ordClass_126000 : ¬ OrdClass 126000 := fun hc =>
  hc.false_of_oddLike (oddLike_of_su3 (p := 5) (N := 126000) (g := 3) (by decide) le_rfl
    (by norm_num) (by norm_num))

theorem not_ordClass_7800 : ¬ OrdClass 7800 := fun hc =>
  hc.false_of_l2sq (p := 5) (by decide) le_rfl (by norm_num)

end CFSG.Quasithin
