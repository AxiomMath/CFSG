module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Torus
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Small
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem exists_prime_five_le_dvd_pow_sub_one_not_dvd_exponent {p f : ℕ} (hp : p.Prime) (hf : 3 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ p ^ f - 1 ∧ ¬ r ∣ f := by
  rcases eq_or_ne p 2 with rfl | hp2
  ·
    rcases eq_or_ne f 6 with rfl | hf6
    · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · obtain ⟨r, hr, hrd, hprim⟩ :=
        CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one f (by omega) hf6
      have hpp : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r f := ⟨hr, hrd, hprim⟩
      have hfr : f < r := uc22p22i_lt_of_primitive hpp (by omega)
      have hr2 : r ≠ 2 := hpp.ne_two (by omega)
      have hr3 : r ≠ 3 := by
        intro h3
        have := hpp.eq_two_of_dvd_three (by omega) (by rw [h3])
        omega
      have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
      refine ⟨r, hr, hr5, hrd, fun hrf => ?_⟩
      exact absurd (Nat.le_of_dvd (by omega : 0 < f) hrf) (not_le.mpr hfr)
  ·
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨ℓ, hℓ, hℓd, hℓprim⟩ :=
      CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 hf
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hpr : (p : ZMod ℓ) ^ f = 1 :=
      (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos f).mp hℓd
    have hord : orderOf (p : ZMod ℓ) = f := by
      rw [orderOf_eq_iff (by omega)]
      exact ⟨hpr, fun k hklt hkpos h => hℓprim k hkpos hklt
        ((CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos k).mpr h)⟩
    have hp0 : (p : ZMod ℓ) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega)] at hpr
      exact zero_ne_one hpr
    have hfℓ : f < ℓ := by
      have hle := Nat.le_of_dvd (by have := hℓ.two_le; omega)
        (hord ▸ ZMod.orderOf_dvd_card_sub_one hp0)
      omega
    have hℓ2 : ℓ ≠ 2 := by
      intro h
      subst h
      have h2d : 2 ∣ p ^ 1 - 1 := by
        obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
        exact ⟨k, by rw [pow_one]; omega⟩
      exact hℓprim 1 (by norm_num) (by omega) h2d
    have hℓ3 : ℓ ≠ 3 := by
      intro h
      subst h
      rcases eq_or_ne p 3 with rfl | hp3'
      · have h1 : 3 ∣ 3 ^ f - (3 ^ f - 1) :=
          Nat.dvd_sub (dvd_pow_self 3 (by omega)) hℓd
        rw [Nat.sub_sub_self (Nat.one_le_pow f 3 (by norm_num))] at h1
        exact absurd h1 (by norm_num)
      · have h3d : 3 ∣ p ^ 2 - 1 := by
          have hmod : p ^ 2 ≡ 1 [MOD 3] := by
            have hcop : Nat.Coprime p 3 :=
              (Nat.Prime.coprime_iff_not_dvd hp).2 fun h3dvd =>
                hp3' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3dvd)
            have := Nat.ModEq.pow_totient hcop
            rw [Nat.totient_prime Nat.prime_three] at this
            simpa using this
          exact (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 p hp.pos)).1 hmod.symm
        exact hℓprim 2 (by norm_num) (by omega) h3d
    have hℓf : ¬ ℓ ∣ f := fun hℓf =>
      absurd (Nat.le_of_dvd (by omega : 0 < f) hℓf) (not_le.mpr hfℓ)
    exact ⟨ℓ, hℓ, hℓ.five_le_of_ne_two_of_ne_three hℓ2 hℓ3, hℓd, hℓf⟩

theorem uc22s213_closed_of_exceptional {M L : Subgroup G}
    (h : (∃ p f : ℕ, LieModel (BarInf L) .G2 0 p f) ∨
      (∃ p f : ℕ, LieModel (BarInf L) .trialityD4 0 p f) ∨
      (∃ f : ℕ, LieModel (BarInf L) .twistedF4 0 2 f) ∨ LieModel (BarInf L) .Tits 0 2 1) :
    S21_3ClosedTorus L ∨ S21_3ClosedSmall M L ∨
      (∃ p f : ℕ, f ≤ 2 ∧ LieModel (BarInf L) .G2 0 p f ∧
        (p = 3 ∨ 3 ≤ CFSG.Open.pRank 3 M)) ∨
      (∃ p f : ℕ, (p ≠ 2 ∨ f ≤ 2) ∧ LieModel (BarInf L) .trialityD4 0 p f) := by
  rcases h with ⟨p, f, hX⟩ | ⟨p, f, hX⟩ | ⟨f, hX⟩ | hX
  ·
    obtain ⟨hp, hf, -⟩ := hX.admissible
    by_cases hf3 : 3 ≤ f
    · obtain ⟨r, hr, hr5, hrd, hrf⟩ := exists_prime_five_le_dvd_pow_sub_one_not_dvd_exponent hp hf3
      exact Or.inl (Or.inr ⟨r, p, f, hr, hr5, hrd, hrf, Or.inl hX⟩)
    · have hf2 : f ≤ 2 := by omega
      by_cases hp3 : p = 3
      · exact Or.inr (Or.inr (Or.inl ⟨p, f, hf2, hX, Or.inl hp3⟩))
      · by_cases hm3 : 3 ≤ CFSG.Open.pRank 3 M
        · exact Or.inr (Or.inr (Or.inl ⟨p, f, hf2, hX, Or.inr hm3⟩))
        · have hm32 : CFSG.Open.pRank 3 M ≤ 2 := by omega
          have hf12 : f = 1 ∨ f = 2 := by omega
          refine Or.inr (Or.inl ⟨?_, hm32⟩)
          rcases hf12 with rfl | rfl
          · exact Or.inr (Or.inr ⟨p, 0, hp3, by simpa using hX⟩)
          · exact Or.inr (Or.inr ⟨p, 1, hp3, by simpa using hX⟩)
  ·
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨-, hf, -⟩ := hX.admissible
      by_cases hf3 : 3 ≤ f
      · obtain ⟨r, hr, hr5, hrd, hrf⟩ := exists_prime_five_le_dvd_pow_sub_one_not_dvd_exponent Nat.prime_two hf3
        exact Or.inl (Or.inr ⟨r, 2, f, hr, hr5, hrd, hrf, Or.inr (Or.inl ⟨rfl, hX⟩)⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨2, f, Or.inr (by omega), hX⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, f, Or.inl hp2, hX⟩))
  ·
    obtain ⟨-, -, -, -, -, hf3⟩ := hX.admissible
    obtain ⟨r, hr, hr5, hrd, hrf⟩ := exists_prime_five_le_dvd_pow_sub_one_not_dvd_exponent Nat.prime_two hf3
    exact Or.inl (Or.inr ⟨r, 2, f, hr, hr5, hrd, hrf, Or.inr (Or.inr ⟨rfl, hX⟩)⟩)
  ·
    exact Or.inl (Or.inl hX)

end CFSG.LocalAnalysis.UniquenessCase.UC22
