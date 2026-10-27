module

public import CFSG.LocalAnalysis.StandardType.GGTPNTwA6Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGALocalRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTwA6_twoLocalRank_le {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} (n : ℕ) (hAbA : Ab ≤ A) (hrank : GGTPNRank 3 X Ab)
    (hnum : GGTPNNum 3 n A Ab) (hn : n ≤ 3 ^ 8) :
    LargeEvenTwoLocalRank 3 X ≤ 7 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) := by
  obtain ⟨hnum1, -⟩ := hnum
  have hcardA : Nat.card A ≤ 3 ^ 7 := by
    have h38 : (3 : ℕ) ^ 8 = 3 * 3 ^ 7 := by norm_num
    rw [h38] at hn
    exact Nat.le_of_mul_le_mul_left (hnum1.trans hn) (by norm_num)
  have hcardAb : Nat.card Ab ≤ 3 ^ 7 := (Subgroup.card_le_of_le hAbA).trans hcardA
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hm7 : m ≤ 7 := by
    rw [hmcard] at hcardAb
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcardAb
  omega

private theorem ggTablePRow_twA6 (n : ℕ) (hd : 3 ∣ 2 ^ n + 1) :
    GGTablePRow 3 (⟨.twA, 6, n⟩ : LargeEvenLabel) (⟨.twA, 8, n⟩ : LargeEvenLabel) := by
  unfold GGTablePRow
  right; right; right; right; right; right; right; left
  refine ⟨rfl, hd, by norm_num, ?_⟩
  exact Or.inr (Or.inl ⟨rfl, by norm_num⟩)

theorem ggTwA6ClRARK_holds :
    GGTablePKnownRK fun p n labJ labX => GGRegimeTwA6 p n labJ labX ∧ GGKacRA labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨rfl, hn8, htJ, hrJ, hqJ⟩, hRA⟩ := hr
  obtain ⟨⟨hloc, hflat, -, hrank, hnum, -, honly, hm⟩, -⟩ := hd
  obtain ⟨hAb, -, -, -⟩ := hflat
  rcases labJ with ⟨tJ, rJ, m⟩
  dsimp only at htJ hrJ
  subst htJ
  subst hrJ
  rcases labX with ⟨tX, rX, nX⟩
  have hperf : commutator X = ⊤ := by
    have hm0 := hm
    unfold GGTPNMarked at hm0
    exact hm0.1
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hm' : GGTPNMarked 3 (fun _ lab => lab = (⟨tX, rX, nX⟩ : LargeEvenLabel)) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  have hcore := split_or_fieldType_of_ggKacRA Nat.prime_three hloc honly hRA hm'
  have hcut := ggTwA6_twoLocalRank_le n hAb hrank hnum hn8
  have h3dvd : 3 ∣ rX + 1 := by
    rcases hRA with ⟨-, hd, -⟩ | ⟨-, hd, -⟩
    · exact hd
    · exact hd
  have hq : (tX = .A ∧ 3 ∣ 2 ^ nX - 1) ∨ (tX = .twA ∧ 3 ∣ 2 ^ nX + 1) := by
    rcases hRA with ⟨ht, -, hq⟩ | ⟨ht, -, hq⟩
    · exact Or.inl ⟨ht, hq⟩
    · exact Or.inr ⟨ht, hq⟩
  have hN : rX + 1 = 3 ∨ rX + 1 = 6 ∨ rX + 1 = 9 := by
    have hlt12 : rX + 1 < 12 := by
      by_contra hcon
      push Not at hcon
      have h9 : 9 ≤ rX + 1 := le_trans (by norm_num) hcon
      have h6 := ggALocalRankSubThree_holds X (⟨tX, rX, nX⟩ : LargeEvenLabel) hΛX hq h3dvd h9
        hhX hperf
      have hcancel : (rX + 1 - 3) + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤
          7 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) := h6.trans hcut
      have hsub : rX + 1 - 3 ≤ 7 := Nat.le_of_add_le_add_right hcancel
      have hle10 : rX + 1 ≤ 10 := by
        have h3 : 3 ≤ rX + 1 := le_trans (by norm_num) h9
        calc rX + 1 = rX + 1 - 3 + 3 := (Nat.sub_add_cancel h3).symm
          _ ≤ 7 + 3 := Nat.add_le_add_right hsub 3
          _ = 10 := by norm_num
      exact absurd hcon (Nat.not_le_of_lt (lt_of_le_of_lt hle10 (by norm_num)))
    obtain ⟨k, hk⟩ := h3dvd
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0] at hk
        simp only [Nat.mul_zero] at hk
        exact absurd hk (Nat.succ_ne_zero rX)
      · exact hkpos
    have hk1 : 1 ≤ k := hkpos
    have hk3 : k ≤ 3 := by
      have h1 : 3 * k < 3 * 4 := by
        rw [hk] at hlt12
        simpa using hlt12
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left h1)
    interval_cases k
    · left; simpa using hk
    · right; left; simpa using hk
    · right; right; simpa using hk
  dsimp only at hcore
  rcases hcore with ⟨a, ds, hsum, hne, hlen, hmem, hbr⟩ | ⟨-, -, hbr⟩
  ·
    rcases hbr with ⟨hΛ', hh'⟩ | ⟨hAg, ha2, hΛ', hh'⟩
    · have hiso : GGLabelIso (⟨tX, a - 1, nX⟩ : LargeEvenLabel) (⟨.twA, 6, m⟩ : LargeEvenLabel) :=
        hrig _ _ _ hΛ' hΛJ hh' hhJ
      have heq := ggLabelIso_twA6_right hiso
      have htX : tX = .twA := congrArg LargeEvenLabel.tag heq
      have hra : a - 1 = 6 := congrArg LargeEvenLabel.rank heq
      have hnX : nX = m := congrArg LargeEvenLabel.n heq
      subst htX
      rw [hnX] at hΛX hhX hq
      have hrX : rX = 8 := by
        rcases hN with h | h | h <;> omega
      subst hrX
      have hqX : 3 ∣ 2 ^ m + 1 := by
        rcases hq with ⟨hA, -⟩ | ⟨-, hd⟩
        · cases hA
        · exact hd
      refine ⟨⟨.twA, 6, m⟩, ⟨.twA, 8, m⟩, hΛJ, hΛX, ggTablePRow_twA6 m hqX, hhJ, hhX⟩
    · have hiso : GGLabelIso (⟨.A, 1, nX⟩ : LargeEvenLabel) (⟨.twA, 6, m⟩ : LargeEvenLabel) :=
        hrig _ _ _ hΛ' hΛJ hh' hhJ
      have heq := ggLabelIso_twA6_right hiso
      have ht : LargeEvenLieTag.A = LargeEvenLieTag.twA := congrArg LargeEvenLabel.tag heq
      cases ht
  ·
    rcases hbr with ⟨-, hΛ', hh'⟩ | ⟨htw, hge3, hΛ', hh'⟩
    · have hiso : GGLabelIso (⟨.A, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel)
          (⟨.twA, 6, m⟩ : LargeEvenLabel) := hrig _ _ _ hΛ' hΛJ hh' hhJ
      have heq := ggLabelIso_twA6_right hiso
      have ht : LargeEvenLieTag.A = LargeEvenLieTag.twA := congrArg LargeEvenLabel.tag heq
      cases ht
    · have hiso : GGLabelIso (⟨.twA, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel)
          (⟨.twA, 6, m⟩ : LargeEvenLabel) := hrig _ _ _ hΛ' hΛJ hh' hhJ
      have heq := ggLabelIso_twA6_right hiso
      have hrk : (rX + 1) / 3 - 1 = 6 := congrArg LargeEvenLabel.rank heq
      have hle9 : rX + 1 ≤ 9 := by
        rcases hN with h | h | h <;> omega
      have hle3 : (rX + 1) / 3 ≤ 3 := by
        calc (rX + 1) / 3 ≤ 9 / 3 := Nat.div_le_div_right hle9
          _ = 3 := by norm_num
      omega

end CFSG.StandardType

end
