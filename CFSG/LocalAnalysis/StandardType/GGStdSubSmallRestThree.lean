module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac

public section

namespace CFSG.StandardType

open CFSG.Assembly StdSubRestThree

@[expose] def GGStdSubSmallRest3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGStdSubSmallRest2Label p lab ∧ ¬ GGStdSubSmallVac3Label p lab ∧ lab.tag ≠ .twF4

theorem ggStdSubSmallInputOn_rest2_of_rest3
    (hF3 : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGStdSubSmallInputOn GGStdSubSmallRest3Label) :
    GGStdSubSmallInputOn GGStdSubSmallRest2Label :=
  ((ggStdSubSmallInputOn_vac3.or (ggStdSubSmallInputOn_twF4 hF3)).or h).mono fun p lab hR => by
    by_cases h1 : GGStdSubSmallVac3Label p lab
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : lab.tag = .twF4
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨hR, h1, h2⟩

theorem two_pow_sq_sub_one_eq (n : ℕ) : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
  have h := Nat.sq_sub_sq (2 ^ n) 1
  rwa [one_pow] at h

theorem ggStdSubSmallRest3Label_cases {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGStdSubSmallRest3Label p lab)
    (hs : LargeEvenSplit p lab) :
    (lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank ∧
        (p ∣ lab.rank + 1 ∨ (lab.n = 1 ∧ 4 ≤ lab.rank))) ∨
      (p = 3 ∧ lab.n = 1 ∧ ((lab.tag = .A ∧ 5 ≤ lab.rank) ∨
        ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank))) ∨
      ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
      lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6 := by
  obtain ⟨⟨⟨hTA, hSy⟩, hV, hU⟩, hV3, hF⟩ := h
  obtain ⟨t, l, n⟩ := lab
  have hn1 : 1 ≤ n := hlab.1
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hsu : LargeEvenUntwisted t → t ≠ .twD → t ≠ .triD4 → p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
    intro hu ht1 ht2
    rcases hs with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact Or.inl h
    · exact absurd hu h
    · exact absurd h (by rintro (h' | h') <;> contradiction)
    · exact Or.inr h
  cases t with
  | A =>
    have h1 : ¬ p ∣ 2 ^ n - 1 := fun h => by
      by_cases hl : p ∣ l + 1
      · exact hTA (Or.inr ⟨rfl, h, hl⟩)
      · exact hTA (Or.inl (Or.inl ⟨rfl, h, hl⟩))
    obtain ⟨hn, hp3⟩ := (hsu trivial (by decide) (by decide)).resolve_left h1
    refine Or.inr (Or.inl ⟨hp3, hn, Or.inl ⟨rfl, ?_⟩⟩)
    by_contra hl
    dsimp only at hl
    exact hV3 (Or.inr (Or.inr (Or.inl ⟨hp3, hn, Or.inl ⟨rfl, by dsimp only; omega⟩⟩)))
  | twA =>
    have hpq : p ∣ 2 ^ n + 1 := dvd_of_largeEvenSplit_twA hs rfl
    have hl2 : 2 ≤ l := hlab.2.1
    have hl3 : 3 ≤ l := by
      by_contra hl3
      exact hV3 (Or.inr (Or.inr (Or.inr ⟨rfl, by dsimp only; omega⟩)))
    by_cases hd : p ∣ l + 1
    · exact Or.inl ⟨rfl, hpq, hl3, Or.inl hd⟩
    · have h2 : ¬ (2 ≤ n ∨ l ≤ 3) := fun h' => hU ⟨⟨Or.inl rfl, hpq⟩, hd, h'⟩
      exact Or.inl ⟨rfl, hpq, hl3, Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩⟩
  | B =>
    have h1 : ¬ p ∣ 2 ^ n - 1 := fun h => hSy ⟨Or.inl rfl, h⟩
    obtain ⟨hn, hp3⟩ := (hsu trivial (by decide) (by decide)).resolve_left h1
    have hl := hlab.2
    dsimp only at hl
    exact Or.inr (Or.inl ⟨hp3, hn, Or.inr ⟨Or.inl rfl, by dsimp only; omega⟩⟩)
  | C =>
    have h1 : ¬ p ∣ 2 ^ n - 1 := fun h => hSy ⟨Or.inr rfl, h⟩
    obtain ⟨hn, hp3⟩ := (hsu trivial (by decide) (by decide)).resolve_left h1
    have hl := hlab.2
    dsimp only at hl
    exact Or.inr (Or.inl ⟨hp3, hn, Or.inr ⟨Or.inr rfl, by dsimp only; omega⟩⟩)
  | D =>
    have hl : 3 ≤ l := hlab.2
    refine Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, ?_⟩))
    dsimp only
    by_contra hl4
    have hl3 : l = 3 := by omega
    subst hl3
    rcases hsu trivial (by decide) (by decide) with h | ⟨hn, hp3⟩
    · exact hTA (Or.inl (Or.inr (Or.inl ⟨rfl, rfl, h⟩)))
    · exact hV3 (Or.inr (Or.inr (Or.inl ⟨hp3, hn, Or.inr ⟨rfl, rfl⟩⟩)))
  | twD =>
    have hl : 2 ≤ l := hlab.2
    refine Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, ?_⟩))
    dsimp only
    by_contra hl4
    have hs' : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 := by
      rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨hn, rfl⟩
      · exact absurd h id
      · exact Or.inl h
      · exact Or.inr h
      · subst hn
        exact Or.inl (by norm_num)
    rcases (show l = 2 ∨ l = 3 by omega) with rfl | rfl
    · apply hTA (Or.inl (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)))
      dsimp only
      rw [two_pow_sq_sub_one_eq]
      rcases hs' with h | h
      · exact Dvd.dvd.mul_right h _
      · exact Dvd.dvd.mul_left h _
    · rcases hs' with h | h
      · have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn1 h
        have h4 : ¬ p ∣ 3 + 1 := fun h4 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
        exact hU ⟨⟨Or.inr ⟨rfl, rfl⟩, h⟩, h4, Or.inr le_rfl⟩
      · exact hV (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h⟩)))
  | E6 => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | E7 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | E8 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | F4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | twE6 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  | triD4 => exact absurd (Or.inl (Or.inr (Or.inl rfl))) hV3
  | G2 => exact absurd (Or.inl rfl) hV
  | twB2 => exact absurd (Or.inr (Or.inl rfl)) hV
  | twF4 => exact absurd rfl hF
  | B2der =>
    have hn : n = 1 := hlab.2.2
    subst hn
    rcases hsu trivial (by decide) (by decide) with h | ⟨-, hp3⟩
    · exact absurd (Nat.dvd_one.mp (by simpa using h)) hp1
    · exact absurd (Or.inr (Or.inr (Or.inr ⟨hp3, rfl⟩))) hV
  | G2der => exact absurd (Or.inl (Or.inl rfl)) hV3
  | twF4der => exact absurd (Or.inr (Or.inl rfl)) hV3

end CFSG.StandardType
