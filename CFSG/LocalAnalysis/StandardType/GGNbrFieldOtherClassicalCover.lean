module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalOrth
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2Rows
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResidualDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2Sp4Rows
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSCRows
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitCop
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitDvd
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitFiveMinus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggFermat_two_pow_cast {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    ((2 ^ n : ℕ) : ZMod p) = ((2 ^ (n / p) : ℕ) : ZMod p) := by
  haveI := Fact.mk hp
  obtain ⟨m, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left m hp.pos, Nat.cast_pow, Nat.cast_pow, pow_mul, ZMod.pow_card]

theorem ggFermat_dvd_two_pow_add_one_iff {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    p ∣ 2 ^ n + 1 ↔ p ∣ 2 ^ (n / p) + 1 := by
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_add,
    ggFermat_two_pow_cast hp hpn]

theorem ggFermat_dvd_two_pow_sub_one_iff {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    p ∣ 2 ^ n - 1 ↔ p ∣ 2 ^ (n / p) - 1 := by
  have h1 : ((2 ^ n - 1 : ℕ) : ZMod p) = ((2 ^ n : ℕ) : ZMod p) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one]
  have h2 : ((2 ^ (n / p) - 1 : ℕ) : ZMod p) = ((2 ^ (n / p) : ℕ) : ZMod p) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one]
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, h1, h2,
    ggFermat_two_pow_cast hp hpn]

theorem ggFermat_eq_three_of_div_eq_one {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (h1 : n / p = 1) (h : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1) : p = 3 ∧ n = 3 := by
  have hn : n = p := by
    have := Nat.mul_div_cancel' hpn
    rw [h1, mul_one] at this
    exact this.symm
  rcases h with h | h
  · rw [ggFermat_dvd_two_pow_add_one_iff hp hpn, h1] at h
    have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h)
    exact ⟨h3, hn.trans h3⟩
  · rw [ggFermat_dvd_two_pow_sub_one_iff hp hpn, h1] at h
    have h' : p = 1 := by simpa using h
    exact absurd h' hp.one_lt.ne'

theorem ggThree_dvd_two_pow_sub_or_add (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  have h : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

@[expose] def GGFieldOtherC9Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylFieldOtherOpenLabel p lab ∧ ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧
    ¬ GGFieldFixD4Label p lab ∧ ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n)

theorem ggFieldOtherC9Label_classical_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hc : GGFieldOtherC9Label p lab)
    (ht : GGFieldClassicalTag lab) :
    GGFieldOtherUnitCopLabel p lab ∨ GGFieldOtherTwOmegaLabel p lab ∨
      GGFieldOtherOmegaEightLabel p lab ∨ GGFieldOtherUnitDvdLabel p lab ∨
      GGFieldOtherSpThreeLabel p lab ∨ GGFieldOtherUnitFourLabel p lab ∨
      GGFieldOtherUnitFiveMinusLabel p lab ∨ GGFieldOtherA2PlusLabel p lab ∨
      GGFieldOtherL4Label p lab ∨ GGFieldOtherU3Label p lab ∨ GGFieldOtherU4Label p lab ∨
      GGFieldOtherSp4Label p lab ∨ GGFieldClassicalResidualLabel p lab := by
  obtain ⟨hOpen, hFF, hFN, hFD, -⟩ := hc
  have hOther := hOpen.1
  have hVO := hOpen.2
  have hFRest := hOther.1
  have hFR := hOther.2.1
  have hFL := hFRest.1
  have hVA2 := hFRest.2
  have hTASC := hFL.1.1.1
  have hLT := hFL.1.1.2
  have hPM := hFL.2.1
  have hNV := hFL.2.2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp1 : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)
  have hpnot2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hpnot4 : ¬ p ∣ 4 := fun h =>
    hpnot2 (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h))
  have hpm : ∀ m : ℕ, p ∣ 2 ^ m - 1 → p ∣ 2 ^ m + 1 → False := fun m h1 h2 => by
    have h1' : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h3 : p ∣ (2 ^ m + 1) - (2 ^ m - 1) := Nat.dvd_sub h2 h1
    rw [show (2 ^ m + 1) - (2 ^ m - 1) = 2 by omega] at h3
    exact hpnot2 h3
  obtain ⟨t, l, n⟩ := lab
  have hn1 : 1 ≤ n := hlab.1
  have hdiv : p ∣ n → 1 ≤ n / p := fun h => Nat.div_pos (Nat.le_of_dvd hn1 h) hp.pos
  rcases ht with ht | ht | ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  ·
    have hdvd : p ∣ n := by
      by_contra h
      exact hPM ⟨Or.inr (Or.inl ⟨Or.inl rfl, h⟩), fun h' => by cases h'.1⟩
    have hl : 1 ≤ l := hlab.2.1
    have hl1 : l ≠ 1 := fun h => hLT (Or.inl ⟨rfl, h⟩)
    rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with rfl | rfl | hl4
    ·
      by_cases hplus : p ∣ 2 ^ n + 1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hdvd, ⟨hplus, rfl, rfl⟩,
            ⟨(ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp hplus, rfl, rfl⟩⟩)))))))
      by_cases hminus : p ∣ 2 ^ n - 1
      · have h3 : p ∣ 2 + 1 := by
          by_contra h3
          exact hTASC (Or.inl ⟨rfl, le_rfl, hminus, h3⟩)
        have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
        subst hp3'
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hminus⟩))))))))))))
      · exfalso
        have hp3' : p = 3 := by
          by_contra h3
          exact hVA2 ⟨hFL, rfl, rfl, h3, hminus, hplus⟩
        subst hp3'
        rcases ggThree_dvd_two_pow_sub_or_add n with h | h
        · exact hminus h
        · exact hplus h
    ·
      have hminus : ¬ p ∣ 2 ^ n - 1 := fun h => hTASC (Or.inl ⟨rfl, by norm_num, h, hpnot4⟩)
      have hplus : p ∣ 2 ^ n + 1 := by
        by_contra h
        exact hVO ⟨hOther, Or.inr (Or.inl ⟨Or.inl rfl, rfl, hminus, h⟩)⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hdvd, ⟨hplus, Or.inl rfl, rfl⟩,
          ⟨(ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp hplus, Or.inl rfl, rfl⟩⟩))))))))
    ·
      exfalso
      have hminus : ¬ p ∣ 2 ^ n - 1 := fun h =>
        hFF ⟨hdvd, h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hl4⟩))))⟩
      have hn3 : p ≤ n := Nat.le_of_dvd hn1 hdvd
      refine hNV (Or.inr (Or.inr (Or.inl ⟨rfl, hl4, hminus, ?_, ?_, ?_⟩)))
      · rintro ⟨h1, -⟩
        dsimp only at h1
        omega
      · rintro ⟨-, h2, h5⟩
        dsimp only at h2
        subst h5 h2
        exact absurd hdvd (by norm_num)
      · rintro ⟨-, h1, -⟩
        dsimp only at h1
        omega
  ·
    have hdvd : p ∣ n := by
      by_contra h
      exact hPM ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, Or.inr (Or.inr ⟨Or.inl rfl, h⟩)⟩)))),
        fun h' => by cases h'.1⟩
    have hl : 2 ≤ l := hlab.2.1
    have hsubp : p ∣ 2 ^ n + 1 → p ∣ 2 ^ (n / p) + 1 :=
      (ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp
    have hsubm : p ∣ 2 ^ n - 1 → p ∣ 2 ^ (n / p) - 1 :=
      (ggFermat_dvd_two_pow_sub_one_iff hp hdvd).mp
    rcases (show l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ 6 ≤ l by omega) with
      rfl | rfl | rfl | rfl | hl6
    ·
      have hplus : p ∣ 2 ^ n + 1 := by
        by_contra h
        exact hVO ⟨hOther, Or.inl ⟨rfl, rfl, h⟩⟩
      by_cases hp3' : p = 3
      · subst hp3'
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hplus⟩)))))))))))))
      · have hp5 : 5 ≤ p := by
          rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h
          · exact absurd h hp3'
          · subst h; exact absurd hp (by norm_num)
          · exact h
        have h2 : 2 ≤ n / p := by
          by_contra h2
          have h1 : n / p = 1 := by have := hdiv hdvd; omega
          have := (ggFermat_eq_three_of_div_eq_one hp hdvd h1 (Or.inl hplus)).1
          omega
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hdvd, h2, ⟨hp5, hplus, rfl, rfl⟩, ⟨hp5, hsubp hplus, rfl, rfl⟩⟩)))))))))
    ·
      by_cases hplus : p ∣ 2 ^ n + 1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hdvd, ⟨hplus, Or.inl rfl, rfl⟩, ⟨hsubp hplus, Or.inl rfl, rfl⟩⟩)))))
      · have hminus : p ∣ 2 ^ n - 1 := by
          by_contra h
          exact hVO ⟨hOther, Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl, h, hplus⟩))⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hdvd, ⟨hminus, Or.inl rfl, rfl⟩, ⟨hsubm hminus, Or.inl rfl, rfl⟩⟩))))))))))
    ·
      have hplus : p ∣ 2 ^ n + 1 := by
        by_contra h
        exact hNV (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, h, fun h' => by dsimp only at h'; omega⟩))))
      by_cases h5 : p ∣ 4 + 1
      · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
        subst hp5
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hplus⟩))))))))))))))
      · exact Or.inl ⟨hdvd, ⟨hplus, rfl, le_rfl, h5⟩, ⟨hsubp hplus, rfl, le_rfl, h5⟩⟩
    ·
      by_cases hplus : p ∣ 2 ^ n + 1
      · have hp3' : p ≠ 3 := fun h => hFR (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h, hplus⟩))))
        have h6 : ¬ p ∣ 5 + 1 := by
          intro h6
          have : p ∣ 2 * 3 := h6
          rcases (Nat.Prime.dvd_mul hp).mp this with h | h
          · exact hpnot2 h
          · exact hp3' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
        exact Or.inl ⟨hdvd, ⟨hplus, rfl, by norm_num, h6⟩, ⟨hsubp hplus, rfl, by norm_num, h6⟩⟩
      · have hminus : p ∣ 2 ^ n - 1 := by
          by_contra h
          exact hNV (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by norm_num, hplus, fun _ => h⟩))))
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hdvd, ⟨hminus, rfl, rfl⟩, ⟨hsubm hminus, rfl, rfl⟩⟩))))))
    ·
      have hplus : p ∣ 2 ^ n + 1 := by
        by_contra h
        exact hNV (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, by dsimp only; omega, h, fun h' => by dsimp only at h'; omega⟩))))
      by_cases hd : p ∣ l + 1
      · have hne : ¬ (l = 5 ∧ p = 3) := fun h => by omega
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hdvd, ⟨hplus, rfl, by dsimp only; omega, hd, hne⟩,
            ⟨hsubp hplus, rfl, by dsimp only; omega, hd, hne⟩⟩)))
      · exact Or.inl ⟨hdvd, ⟨hplus, rfl, by dsimp only; omega, hd⟩,
          ⟨hsubp hplus, rfl, by dsimp only; omega, hd⟩⟩
  ·
    have hdvd : p ∣ n := by
      by_contra h
      exact hPM ⟨Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, h⟩)), fun h' => by cases h'.1⟩
    have hl : 2 ≤ l := hlab.2.1
    have hq : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 := by
      by_contra h
      push Not at h
      exact hNV (Or.inl ⟨Or.inl rfl, h.2, h.1⟩)
    have hsubp : p ∣ 2 ^ n + 1 → p ∣ 2 ^ (n / p) + 1 :=
      (ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp
    have hsubm : p ∣ 2 ^ n - 1 → p ∣ 2 ^ (n / p) - 1 :=
      (ggFermat_dvd_two_pow_sub_one_iff hp hdvd).mp
    rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with rfl | rfl | hl4
    ·
      by_cases h2 : 2 ≤ n / p
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdvd, h2, ⟨hq, Or.inl rfl, rfl⟩, ⟨hq.imp hsubp hsubm, Or.inl rfl, rfl⟩⟩)))))))))))
      · have h1 : n / p = 1 := by have := hdiv hdvd; omega
        obtain ⟨hp3', hn3⟩ := ggFermat_eq_three_of_div_eq_one hp hdvd h1 hq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, rfl, hp3', hn3⟩)))))))))))))))
    ·
      have hminus : ¬ p ∣ 2 ^ n - 1 := fun h =>
        hFF ⟨hdvd, h, Or.inr (Or.inl ⟨Or.inl rfl, by norm_num⟩)⟩
      have hplus : p ∣ 2 ^ n + 1 := hq.resolve_right hminus
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdvd, ⟨hplus, Or.inl rfl, rfl⟩, ⟨hsubp hplus, Or.inl rfl, rfl⟩⟩))))
    ·
      exfalso
      have hminus : ¬ p ∣ 2 ^ n - 1 := fun h =>
        hFF ⟨hdvd, h, Or.inr (Or.inl ⟨Or.inl rfl, by dsimp only; omega⟩)⟩
      have hplus : p ∣ 2 ^ n + 1 := hq.resolve_right hminus
      exact hFN ⟨hdvd, ⟨hplus, Or.inl ⟨Or.inl rfl, hl4⟩⟩, ⟨hsubp hplus, Or.inl ⟨Or.inl rfl, hl4⟩⟩⟩
  ·
    have hdvd : p ∣ n := by
      by_contra h
      exact hPM ⟨Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), h⟩)), fun h' => by cases h'.1⟩
    have hl : 2 ≤ l := hlab.2.1
    have hq : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 := by
      by_contra h
      push Not at h
      exact hNV (Or.inl ⟨Or.inr rfl, h.2, h.1⟩)
    have hsubp : p ∣ 2 ^ n + 1 → p ∣ 2 ^ (n / p) + 1 :=
      (ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp
    have hsubm : p ∣ 2 ^ n - 1 → p ∣ 2 ^ (n / p) - 1 :=
      (ggFermat_dvd_two_pow_sub_one_iff hp hdvd).mp
    rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with rfl | rfl | hl4
    ·
      by_cases h2 : 2 ≤ n / p
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdvd, h2, ⟨hq, Or.inr rfl, rfl⟩, ⟨hq.imp hsubp hsubm, Or.inr rfl, rfl⟩⟩)))))))))))
      · have h1 : n / p = 1 := by have := hdiv hdvd; omega
        obtain ⟨hp3', hn3⟩ := ggFermat_eq_three_of_div_eq_one hp hdvd h1 hq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, rfl, hp3', hn3⟩)))))))))))))))
    ·
      have hminus : ¬ p ∣ 2 ^ n - 1 := fun h =>
        hFF ⟨hdvd, h, Or.inr (Or.inl ⟨Or.inr rfl, by norm_num⟩)⟩
      have hplus : p ∣ 2 ^ n + 1 := hq.resolve_right hminus
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdvd, ⟨hplus, Or.inr rfl, rfl⟩, ⟨hsubp hplus, Or.inr rfl, rfl⟩⟩))))
    ·
      exfalso
      have hminus : ¬ p ∣ 2 ^ n - 1 := fun h =>
        hFF ⟨hdvd, h, Or.inr (Or.inl ⟨Or.inr rfl, by dsimp only; omega⟩)⟩
      have hplus : p ∣ 2 ^ n + 1 := hq.resolve_right hminus
      exact hFN ⟨hdvd, ⟨hplus, Or.inl ⟨Or.inr rfl, hl4⟩⟩, ⟨hsubp hplus, Or.inl ⟨Or.inr rfl, hl4⟩⟩⟩
  ·
    have hl : 3 ≤ l := hlab.2
    rcases (show l = 3 ∨ 4 ≤ l by omega) with rfl | hl4
    ·
      have hdvd : p ∣ n := by
        by_contra h
        exact hPM ⟨Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, h⟩), fun h' => by
          have h4 := h'.2.1
          dsimp only at h4
          omega⟩
      have hminus : ¬ p ∣ 2 ^ n - 1 := fun h => hTASC (Or.inr ⟨rfl, rfl, h, hpnot4⟩)
      have hplus : p ∣ 2 ^ n + 1 := by
        by_contra h
        exact hVO ⟨hOther, Or.inr (Or.inl ⟨Or.inr rfl, rfl, hminus, h⟩)⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdvd, ⟨hplus, Or.inr rfl, rfl⟩,
        ⟨(ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp hplus, Or.inr rfl, rfl⟩⟩))))))))
    · by_cases h43 : l = 4 ∧ p = 3
      · obtain ⟨rfl, rfl⟩ := h43
        have hn : n = 1 ∨ n = 3 := by
          by_contra h
          push Not at h
          exact hFD ⟨rfl, rfl, rfl, show 2 ≤ n by omega, h.2⟩
        exact Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, rfl, hn⟩))
      · have hdvd : p ∣ n := by
          by_contra h
          exact hPM ⟨Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr ⟨rfl, hl4⟩), h⟩)), fun h' =>
            h43 ⟨h'.2.1, h'.2.2⟩⟩
        have hn2 : 2 ≤ n := by
          by_contra h
          have h1 : n = 1 := by omega
          exact hPM ⟨Or.inl ⟨h1, Or.inr (Or.inr (Or.inl ⟨rfl, hl4⟩))⟩, fun h' =>
            h43 ⟨h'.2.1, h'.2.2⟩⟩
        have hminus : ¬ p ∣ 2 ^ n - 1 := fun h =>
          hFF ⟨hdvd, h, Or.inr (Or.inr (Or.inl ⟨rfl, hl4, h43⟩))⟩
        have hplus : p ∣ 2 ^ n + 1 := by
          by_contra h
          exact hNV (Or.inr (Or.inl ⟨Or.inl rfl, hl4, hminus, h⟩))
        have hsubp := (ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp hplus
        by_cases h2 : 2 ≤ n / p
        · exfalso
          exact hFN ⟨hdvd, ⟨hplus, Or.inr (Or.inl ⟨rfl, hl4, h43, hn2⟩)⟩,
            ⟨hsubp, Or.inr (Or.inl ⟨rfl, hl4, h43, h2⟩)⟩⟩
        · have h1 : n / p = 1 := by have := hdiv hdvd; omega
          obtain ⟨hp3', hn3⟩ := ggFermat_eq_three_of_div_eq_one hp hdvd h1 (Or.inl hplus)
          exact Or.inr (Or.inr (Or.inl ⟨rfl, hl4, hp3', Or.inr hn3⟩))
  ·
    have hl : 2 ≤ l := hlab.2
    rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with rfl | rfl | hl4
    · exact absurd (Or.inr ⟨rfl, rfl⟩) hLT
    ·
      have hdvd : p ∣ n := by
        by_contra h
        exact hPM ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hp2, Or.inr (Or.inr ⟨Or.inr ⟨rfl, rfl⟩, h⟩)⟩)))), fun h' => by cases h'.1⟩
      by_cases hplus : p ∣ 2 ^ n + 1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdvd, ⟨hplus, Or.inr rfl, rfl⟩,
          ⟨(ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp hplus, Or.inr rfl, rfl⟩⟩)))))
      · have hminus : p ∣ 2 ^ n - 1 := by
          by_contra h
          exact hVO ⟨hOther, Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, rfl, h, hplus⟩))⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdvd, ⟨hminus, Or.inr rfl, rfl⟩,
          ⟨(ggFermat_dvd_two_pow_sub_one_iff hp hdvd).mp hminus, Or.inr rfl, rfl⟩⟩))))))))))
    ·
      have hdvd : p ∣ n := by
        by_contra h
        exact hPM ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, Or.inl ⟨rfl, hl4, h⟩⟩)))),
          fun h' => by cases h'.1⟩
      have hminus : ¬ p ∣ 2 ^ n - 1 := fun h =>
        hFF ⟨hdvd, h, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hl4⟩)))⟩
      have hplus : p ∣ 2 ^ n + 1 := by
        by_contra h
        exact hNV (Or.inr (Or.inl ⟨Or.inr rfl, hl4, hminus, h⟩))
      exact Or.inr (Or.inl ⟨hdvd, ⟨hplus, rfl, hl4⟩,
        ⟨(ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp hplus, rfl, hl4⟩⟩)

section Head

theorem ggNbrInnerWeylOn_c9_of_nonClassicalExc (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (h : GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab ∧
      ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n) ∧
      (¬ GGFieldClassicalTag lab ∨ GGFieldClassicalResidualLabel p lab)) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab ∧
      ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n) := by
  refine ggNbrInnerWeylOn_of_unitCop hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_twOmegaAll hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_omegaEight hL hPJ hG hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_unitDvd hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_spThree hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_unitFour hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_unitFiveMinus hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_a2Plus hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_l4 hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_u3 hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_u4 hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_sp4 hL hPJ hG hpc hconj hcen hinn ?_
  refine h.mono_of_lambda fun p lab hp hp2 hlab hr => ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hr
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, ?_⟩
  by_cases ht : GGFieldClassicalTag lab
  · right
    rcases ggFieldOtherC9Label_classical_cover hp hp2 hlab hc ht with
      h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact absurd h h4
    · exact absurd h h5
    · exact absurd h h6
    · exact absurd h h7
    · exact absurd h h8
    · exact absurd h h9
    · exact absurd h h10
    · exact absurd h h11
    · exact absurd h h12
    · exact h
  · exact Or.inl ht

end Head

end CFSG.StandardType

end
