module

public import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2Defs
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem rc_cover {p : ℕ} {lab : LargeEvenLabel} (hcov : ¬ GGTBTorCov p lab) :
    ∀ {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)},
      ¬ GGTBTorRowAt p lab r m N C M :=
  fun h => hcov ⟨_, _, _, _, _, h⟩

private theorem rc_not_both {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ (p ∣ 2 ^ n - 1 ∧ p ∣ 2 ^ n + 1) := by
  rintro ⟨h1, h2⟩
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hsub : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
  have hd : p ∣ 2 := by
    rw [← hsub]
    exact Nat.dvd_sub h2 h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

private theorem rc_cases_A {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 1 ≤ r)
    (hr1 : r = 1 → 2 ≤ n) (hcov : ¬ GGTBTorCov p ⟨.A, r, n⟩)
    (hHS : LargeEvenHalfSplit p ⟨.A, r, n⟩ True)
    (hseven : ¬ ggRowSeven p ⟨.A, r, n⟩ ⟨.A, r, n⟩)
    (hsmall : ¬ GGTBResSmallLabel p ⟨.A, r, n⟩) : 6 ≤ r ∧ n = 1 ∧ p = 3 := by
  have hboth := rc_not_both (n := n) hp hp2
  have hp3le : 3 ≤ p := by have := hp.two_le; omega
  have key : n = 1 → p = 3 → 6 ≤ r ∧ n = 1 ∧ p = 3 := by
    intro hn1 hp3
    refine ⟨?_, hn1, hp3⟩
    by_contra hlt
    have hlt' : r < 6 := by omega
    have hr5 : r = 5 ∨ r ≤ 4 := by omega
    rcases hr5 with hr5 | hr4
    · subst hn1 hp3 hr5
      exact rc_cover hcov (GGTBTorRowAt.relA5 rfl (Or.inl ⟨rfl, by norm_num⟩))
    · refine hsmall ?_
      unfold GGTBResSmallLabel
      have h4 : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
      rcases h4 with h | h | h | h
      · exfalso
        have := hr1 h
        omega
      · exact Or.inl ⟨rfl, Or.inl h⟩
      · exact Or.inl ⟨rfl, Or.inr ⟨Or.inl h, hn1, hp3⟩⟩
      · exact Or.inl ⟨rfl, Or.inr ⟨Or.inr h, hn1, hp3⟩⟩
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exfalso
      by_cases hd : p ∣ r + 1
      · by_cases hr4 : 4 ≤ r
        · exact rc_cover hcov (GGTBTorRowAt.aDep (Or.inl rfl) hr4 hd
            (by simpa [ggTorM] using h1) (fun h => hboth ⟨h1, h.2.2⟩))
        · refine hsmall ?_
          unfold GGTBResSmallLabel
          have hle : p ≤ r + 1 := Nat.le_of_dvd (by omega) hd
          have hp4 : p ≤ 4 := by omega
          interval_cases p
          · have h2 : r = 2 := by omega
            exact Or.inl ⟨rfl, Or.inl h2⟩
          · exact absurd hp (by norm_num)
      · exact rc_cover hcov (GGTBTorRowAt.aInd (Or.inl rfl) hd (by simpa [ggTorM] using h1))
    · exfalso
      first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · exfalso
      simp at ht
    · exact key hn1 hp3
  · exfalso
    obtain ⟨ht, -⟩ := hH2
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH3
    simp at ht
  · exfalso
    obtain ⟨-, hr5, hn2, -, hp5⟩ := hH4
    have hr5' : r = 5 := hr5
    have hn2' : n = 2 := hn2
    subst hr5' hn2' hp5
    exact rc_cover hcov (GGTBTorRowAt.relA5 rfl (Or.inl ⟨rfl, by norm_num⟩))
  · exfalso
    obtain ⟨-, hr8, hn1, hp7⟩ := hH5
    have hr8' : r = 8 := hr8
    have hn1' : n = 1 := hn1
    subst hr8' hn1' hp7
    exact hseven ⟨rfl, Or.inl rfl⟩
  · exfalso
    obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_twA {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hcov : ¬ GGTBTorCov p ⟨.twA, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.twA, r, n⟩ True)
    (hA5 : ¬ (r = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ n + 1))
    (hsmall : ¬ GGTBResSmallLabel p ⟨.twA, r, n⟩) : False := by
  have hp3le : 3 ≤ p := by have := hp.two_le; omega
  have key : p ∣ 2 ^ n + 1 → False := by
    intro h3
    by_cases hd : p ∣ r + 1
    · by_cases hr4 : 4 ≤ r
      · exact rc_cover hcov (GGTBTorRowAt.aDep (Or.inr rfl) hr4 hd (by simpa [ggTorM] using h3)
          (fun h => by
            obtain ⟨hp3, hr5, hd3⟩ := h
            subst hp3
            exact hA5 ⟨hr5, rfl, hd3⟩))
      · refine hsmall ?_
        unfold GGTBResSmallLabel
        have hle : p ≤ r + 1 := Nat.le_of_dvd (by omega) hd
        have hp4 : p ≤ 4 := by omega
        interval_cases p
        · have h2 : r = 2 := by omega
          exact Or.inr (Or.inl ⟨rfl, h2⟩)
        · exact absurd hp (by norm_num)
    · exact rc_cover hcov (GGTBTorRowAt.aInd (Or.inr rfl) hd (by simpa [ggTorM] using h3))
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨hu, -⟩ | ⟨-, -, h3⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · first | exact (hu : False).elim | simp [LargeEvenUntwisted] at hu
    · exact key h3
    · simp at ht
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact key (by norm_num)
  · obtain ⟨ht, -⟩ := hH2
    simp at ht
  · obtain ⟨ht | ht, h1⟩ := hH3
    · obtain ⟨-, hr5⟩ := ht
      exact rc_cover hcov (GGTBTorRowAt.relA5 hr5 (Or.inr ⟨rfl, h1⟩))
    · simp at ht
  · obtain ⟨ht, -⟩ := hH4
    simp at ht
  · obtain ⟨ht, -⟩ := hH5
    simp at ht
  · obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_B {p r n : ℕ} (hp : p.Prime)
    (hcov : ¬ GGTBTorCov p ⟨.B, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.B, r, n⟩ True) : False := by
  have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) ↔ p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := hp.dvd_mul
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exact rc_cover hcov (GGTBTorRowAt.c (Or.inl rfl) (hprod.mpr (Or.inl h1)))
    · first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · simp at ht
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact rc_cover hcov (GGTBTorRowAt.c (Or.inl rfl) (by norm_num))
  · exact rc_cover hcov (GGTBTorRowAt.c (Or.inl rfl) (hprod.mpr (Or.inr hH2.2)))
  · obtain ⟨ht, -⟩ := hH3
    simp at ht
  · obtain ⟨ht, -⟩ := hH4
    simp at ht
  · obtain ⟨ht, -⟩ := hH5
    simp at ht
  · obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_C {p r n : ℕ} (hp : p.Prime)
    (hcov : ¬ GGTBTorCov p ⟨.C, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.C, r, n⟩ True) : False := by
  have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) ↔ p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := hp.dvd_mul
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exact rc_cover hcov (GGTBTorRowAt.c (Or.inr rfl) (hprod.mpr (Or.inl h1)))
    · first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · simp at ht
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact rc_cover hcov (GGTBTorRowAt.c (Or.inr rfl) (by norm_num))
  · obtain ⟨ht, -⟩ := hH2
    simp at ht
  · obtain ⟨ht, -⟩ := hH3
    simp at ht
  · obtain ⟨ht, -⟩ := hH4
    simp at ht
  · obtain ⟨ht, -⟩ := hH5
    simp at ht
  · obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_D {p r n : ℕ}
    (hcov : ¬ GGTBTorCov p ⟨.D, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.D, r, n⟩ True) : False := by
  have key3 : p ∣ 2 ^ n + 1 → False := by
    intro h3
    rcases Nat.even_or_odd r with he | ho
    · exact rc_cover hcov (GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inr ⟨h3, he⟩⟩))
    · exact rc_cover hcov (GGTBTorRowAt.relD (Or.inl ⟨rfl, h3, ho⟩))
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exact rc_cover hcov (GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inl h1⟩))
    · first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · simp at ht
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact key3 (by norm_num)
  · exact key3 hH2.2
  · obtain ⟨ht, -⟩ := hH3
    simp at ht
  · obtain ⟨ht, -⟩ := hH4
    simp at ht
  · obtain ⟨ht, -⟩ := hH5
    simp at ht
  · obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_twD {p r n : ℕ}
    (hcov : ¬ GGTBTorCov p ⟨.twD, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.twD, r, n⟩ True) :
    False := by
  have key1 : p ∣ 2 ^ n - 1 → False := fun h1 =>
    rc_cover hcov (GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inl h1⟩))
  have key3 : p ∣ 2 ^ n + 1 → False := by
    intro h3
    rcases Nat.even_or_odd r with he | ho
    · exact rc_cover hcov (GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inr ⟨h3, he⟩⟩))
    · exact rc_cover hcov (GGTBTorRowAt.d (Or.inr ⟨rfl, h3, ho⟩))
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨hu, -⟩ | ⟨-, -, h3⟩ | ⟨-, h1⟩ | ⟨hn1, hp3⟩
    · first | exact (hu : False).elim | simp [LargeEvenUntwisted] at hu
    · exact key3 h3
    · exact key1 h1
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact key3 (by norm_num)
  · obtain ⟨ht, -⟩ := hH2
    simp at ht
  · obtain ⟨ht, -⟩ := hH3
    simp at ht
  · obtain ⟨ht, -⟩ := hH4
    simp at ht
  · obtain ⟨ht, -⟩ := hH5
    simp at ht
  · obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_E6 {p r n : ℕ} (hr : r = 0)
    (hcov : ¬ GGTBTorCov p ⟨.E6, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.E6, r, n⟩ True)
    (hseven : ¬ ggRowSeven p ⟨.E6, r, n⟩ ⟨.E6, r, n⟩) : n = 1 ∧ p = 3 := by
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exfalso
      by_cases hp3 : p = 3
      · subst hp3
        exact rc_cover hcov (GGTBTorRowAt.e6Three rfl rfl (by simpa [ggTorM] using h1))
      · exact rc_cover hcov (GGTBTorRowAt.e6Ind hp3 (Or.inl rfl) (by simpa [ggTorM] using h1))
    · exfalso
      first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · exfalso
      simp at ht
    · exact ⟨hn1, hp3⟩
  · exfalso
    obtain ⟨ht, -⟩ := hH2
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH3
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH4
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH5
    simp at ht
  · exfalso
    obtain ⟨-, hn1, hp7⟩ := hH6
    have hn1' : n = 1 := hn1
    subst hr hn1' hp7
    exact hseven ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩

private theorem rc_cases_E7 {p r n : ℕ} (hp : p.Prime)
    (hcov : ¬ GGTBTorCov p ⟨.E7, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.E7, r, n⟩ True) : False := by
  have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) ↔ p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := hp.dvd_mul
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exact rc_cover hcov (GGTBTorRowAt.e7 rfl (hprod.mpr (Or.inl h1)))
    · first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · simp at ht
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact rc_cover hcov (GGTBTorRowAt.e7 rfl (by norm_num))
  · exact rc_cover hcov (GGTBTorRowAt.e7 rfl (hprod.mpr (Or.inr hH2.2)))
  · obtain ⟨ht, -⟩ := hH3
    simp at ht
  · obtain ⟨ht, -⟩ := hH4
    simp at ht
  · obtain ⟨ht, -⟩ := hH5
    simp at ht
  · obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_E8 {p r n : ℕ} (hp : p.Prime)
    (hcov : ¬ GGTBTorCov p ⟨.E8, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.E8, r, n⟩ True) : False := by
  have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) ↔ p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := hp.dvd_mul
  have key : p ∣ (2 ^ n - 1) * (2 ^ n + 1) → False := by
    intro h
    by_cases hp3 : p = 3
    · exact rc_cover hcov (GGTBTorRowAt.e8Three rfl hp3)
    · exact rc_cover hcov (GGTBTorRowAt.e8Ind hp3 rfl h)
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exact key (hprod.mpr (Or.inl h1))
    · first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · simp at ht
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact key (by norm_num)
  · exact key (hprod.mpr (Or.inr hH2.2))
  · obtain ⟨ht, -⟩ := hH3
    simp at ht
  · obtain ⟨ht, -⟩ := hH4
    simp at ht
  · obtain ⟨ht, -⟩ := hH5
    simp at ht
  · obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_F4 {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcov : ¬ GGTBTorCov p ⟨.F4, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.F4, r, n⟩ True) :
    p = 3 ∧ 3 ∣ 2 ^ n + 1 := by
  have hboth := rc_not_both (n := n) hp hp2
  have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) ↔ p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := hp.dvd_mul
  have key3 : p ∣ 2 ^ n + 1 → p = 3 ∧ 3 ∣ 2 ^ n + 1 := by
    intro h3
    by_cases hp3 : p = 3
    · subst hp3
      exact ⟨rfl, h3⟩
    · exact (rc_cover hcov (GGTBTorRowAt.f4 rfl (hprod.mpr (Or.inr h3))
        (fun h => hp3 h.1))).elim
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exact (rc_cover hcov (GGTBTorRowAt.f4 rfl (hprod.mpr (Or.inl h1))
        (fun h => hboth ⟨h1, h.2⟩))).elim
    · exfalso
      first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · exfalso
      simp at ht
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact ⟨rfl, by norm_num⟩
  · exact key3 hH2.2
  · exfalso
    obtain ⟨ht, -⟩ := hH3
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH4
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH5
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_G2 {p r n : ℕ} (hn2 : 2 ≤ n)
    (hcov : ¬ GGTBTorCov p ⟨.G2, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.G2, r, n⟩ True) : False := by
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | ⟨hn1, -⟩
    · exact rc_cover hcov (GGTBTorRowAt.g2 rfl h1)
    · first | exact hnu trivial | simp [LargeEvenUntwisted] at hnu
    · simp at ht
    · have hn1' : n = 1 := hn1
      omega
  · obtain ⟨ht, -⟩ := hH2
    simp at ht
  · obtain ⟨ht, -⟩ := hH3
    simp at ht
  · obtain ⟨ht, -⟩ := hH4
    simp at ht
  · obtain ⟨ht, -⟩ := hH5
    simp at ht
  · obtain ⟨ht, -⟩ := hH6
    simp at ht

private theorem rc_cases_twE6 {p r n : ℕ}
    (hcov : ¬ GGTBTorCov p ⟨.twE6, r, n⟩) (hHS : LargeEvenHalfSplit p ⟨.twE6, r, n⟩ True) :
    p = 3 ∧ (3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) := by
  have key1 : p ∣ 2 ^ n - 1 → p = 3 ∧ 3 ∣ 2 ^ n - 1 := by
    intro h1
    by_cases hp3 : p = 3
    · subst hp3
      exact ⟨rfl, h1⟩
    · exact (rc_cover hcov (GGTBTorRowAt.relE6 hp3 (Or.inr ⟨rfl, h1⟩))).elim
  have key3 : p ∣ 2 ^ n + 1 → p = 3 ∧ 3 ∣ 2 ^ n + 1 := by
    intro h3
    by_cases hp3 : p = 3
    · subst hp3
      exact ⟨rfl, h3⟩
    · exact (rc_cover hcov (GGTBTorRowAt.e6Ind hp3 (Or.inr rfl)
        (by simpa [ggTorM] using h3))).elim
  rcases hHS with hS | hH2 | hH3 | hH4 | hH5 | hH6
  · rcases hS with ⟨hu, -⟩ | ⟨-, -, h3⟩ | ⟨ht, -⟩ | ⟨hn1, hp3⟩
    · exfalso
      first | exact (hu : False).elim | simp [LargeEvenUntwisted] at hu
    · exact ⟨(key3 h3).1, Or.inr (key3 h3).2⟩
    · exfalso
      simp at ht
    · have hn1' : n = 1 := hn1
      subst hn1' hp3
      exact ⟨rfl, Or.inr (by norm_num)⟩
  · exfalso
    obtain ⟨ht, -⟩ := hH2
    simp at ht
  · obtain ⟨-, h1⟩ := hH3
    exact ⟨(key1 h1).1, Or.inl (key1 h1).2⟩
  · exfalso
    obtain ⟨ht, -⟩ := hH4
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH5
    simp at ht
  · exfalso
    obtain ⟨ht, -⟩ := hH6
    simp at ht

theorem ggTBWeylRowResRest2_cases {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 lab) (h : GGTBWeylRowResRest2 p lab) :
    (lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3) ∨ GGF4ThreeLabel p lab ∨
      GGNbrNonSplitE6TwoLabel p lab ∨ (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      GGTwE6BadLabel p lab := by
  obtain ⟨⟨⟨hcov, hHS, hseven, hF4, hF4d⟩, hA5⟩, hsmall⟩ := h
  rcases lab with ⟨t, r, n⟩
  cases t
  ·
    have hΛ : 1 ≤ n ∧ 1 ≤ r ∧ (r = 1 → 2 ≤ n) := hlab
    obtain ⟨h6, hn1, hp3⟩ := rc_cases_A hp hp2 hΛ.2.1 hΛ.2.2 hcov hHS hseven hsmall
    exact Or.inl ⟨rfl, h6, hn1, hp3⟩
  ·
    have hΛ : 1 ≤ n ∧ 2 ≤ r ∧ (r = 2 → 2 ≤ n) := hlab
    exact (rc_cases_twA hp hp2 hΛ.2.1 hcov hHS (fun h' => hA5 ⟨rfl, h'⟩) hsmall).elim
  · exact (rc_cases_B hp hcov hHS).elim
  · exact (rc_cases_C hp hcov hHS).elim
  · exact (rc_cases_D hcov hHS).elim
  · exact (rc_cases_twD hcov hHS).elim
  ·
    have hΛ : 1 ≤ n ∧ r = 0 := hlab
    obtain ⟨hn1, hp3⟩ := rc_cases_E6 hΛ.2 hcov hHS hseven
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hn1, hp3⟩))
  · exact (rc_cases_E7 hp hcov hHS).elim
  · exact (rc_cases_E8 hp hcov hHS).elim
  ·
    obtain ⟨hp3, h3⟩ := rc_cases_F4 hp hp2 hcov hHS
    exact Or.inr (Or.inl ⟨rfl, hp3, h3⟩)
  ·
    obtain ⟨hp3, h1 | h3⟩ := rc_cases_twE6 hcov hHS
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hp3, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hp3, h3⟩)))
  ·
    exact (hsmall (by unfold GGTBResSmallLabel; simp)).elim
  ·
    have hΛ : 1 ≤ n ∧ r = 0 ∧ 2 ≤ n := hlab
    exact (rc_cases_G2 hΛ.2.2 hcov hHS).elim
  ·
    exact (hsmall (by unfold GGTBResSmallLabel; simp)).elim
  ·
    exact (hF4 rfl).elim
  ·
    exact (hsmall (by unfold GGTBResSmallLabel; simp)).elim
  ·
    exact (hsmall (by unfold GGTBResSmallLabel; simp)).elim
  ·
    exact (hF4d rfl).elim

end CFSG.StandardType

end
