module

public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGALocalRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggLine_twoLocalRank_le {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} (n : ℕ) (hAbA : Ab ≤ A) (hrank : GGTPNRank 3 X Ab)
    (hnum : GGTPNNum 3 n A Ab) (hn : n ≤ 3 ^ 5) :
    LargeEvenTwoLocalRank 3 X ≤ 4 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) := by
  obtain ⟨hnum1, -⟩ := hnum
  have hcardA : Nat.card A ≤ 3 ^ 4 := by
    have h35 : (3 : ℕ) ^ 5 = 3 * 3 ^ 4 := by norm_num
    rw [h35] at hn
    exact Nat.le_of_mul_le_mul_left (hnum1.trans hn) (by norm_num)
  have hcardAb : Nat.card Ab ≤ 3 ^ 4 := (Subgroup.card_le_of_le hAbA).trans hcardA
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hm4 : m ≤ 4 := by
    rw [hmcard] at hcardAb
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcardAb
  omega

private theorem ggResLineJLabel_rank_of_three_dvd_sub {T : GGResLineJType} {r n : ℕ}
    (h : ggResLineJLabel T (⟨.A, r, n⟩ : LargeEvenLabel)) (hd : 3 ∣ 2 ^ n - 1) :
    r = 2 ∨ r = 3 := by
  cases T <;> simp [ggResLineJLabel] at h
  · exact Or.inl h.1
  · exact (three_not_dvd_both_pow_two hd h.2).elim
  · exact Or.inr h.1
  · exact (three_not_dvd_both_pow_two hd h.2).elim
  · exact (three_not_dvd_both_pow_two hd h.2).elim

private theorem ggResLineJLabel_rank_of_three_dvd_add {T : GGResLineJType} {r n : ℕ}
    (h : ggResLineJLabel T (⟨.twA, r, n⟩ : LargeEvenLabel)) (hd : 3 ∣ 2 ^ n + 1) :
    r = 2 ∨ r = 3 := by
  cases T <;> simp [ggResLineJLabel] at h
  · exact Or.inl h.1
  · exact (three_not_dvd_both_pow_two h.2 hd).elim
  · exact Or.inr h.1
  · exact (three_not_dvd_both_pow_two h.2 hd).elim
  · exact (three_not_dvd_both_pow_two h.2 hd).elim

private theorem ggTablePRow_line_A3 (n : ℕ) (hd : 3 ∣ 2 ^ n - 1) :
    GGTablePRow 3 (⟨.A, 3, n⟩ : LargeEvenLabel) (⟨.A, 5, n⟩ : LargeEvenLabel) := by
  unfold GGTablePRow
  left
  refine ⟨rfl, hd, by norm_num, ?_⟩
  exact Or.inr (Or.inl ⟨rfl, by norm_num⟩)

private theorem ggTablePRow_line_twA3 (n : ℕ) (hd : 3 ∣ 2 ^ n + 1) :
    GGTablePRow 3 (⟨.twA, 3, n⟩ : LargeEvenLabel) (⟨.twA, 5, n⟩ : LargeEvenLabel) := by
  unfold GGTablePRow
  right; right; right; right; right; right; right; left
  refine ⟨rfl, hd, by norm_num, ?_⟩
  exact Or.inr (Or.inl ⟨rfl, by norm_num⟩)

theorem ggLineClRARK_holds :
    GGTablePKnownRK fun p n labJ labX => GGRegimeLine p n labJ labX ∧ GGKacRA labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨rfl, hn5, T, hT⟩, hRA⟩ := hr
  obtain ⟨⟨hloc, hflat, -, hrank, hnum, -, honly, hm⟩, -⟩ := hd
  obtain ⟨hAb, -, -, -⟩ := hflat
  rcases labX with ⟨tX, rX, nX⟩
  have hperf : commutator X = ⊤ := by
    have hm0 := hm
    unfold GGTPNMarked at hm0
    exact hm0.1
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hm' : GGTPNMarked 3 (fun _ lab => lab = (⟨tX, rX, nX⟩ : LargeEvenLabel)) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  have hcore := split_or_fieldType_of_ggKacRA Nat.prime_three hloc honly hRA hm'
  have hcut := ggLine_twoLocalRank_le n hAb hrank hnum hn5
  have h3dvd : 3 ∣ rX + 1 := by
    rcases hRA with ⟨-, hd, -⟩ | ⟨-, hd, -⟩
    · exact hd
    · exact hd
  have hq : (tX = .A ∧ 3 ∣ 2 ^ nX - 1) ∨ (tX = .twA ∧ 3 ∣ 2 ^ nX + 1) := by
    rcases hRA with ⟨ht, -, hq⟩ | ⟨ht, -, hq⟩
    · exact Or.inl ⟨ht, hq⟩
    · exact Or.inr ⟨ht, hq⟩
  have hN : rX + 1 = 3 ∨ rX + 1 = 6 := by
    have hlt9 : rX + 1 < 9 := by
      by_contra hcon
      push Not at hcon
      have h6 := ggALocalRankThree_holds X (⟨tX, rX, nX⟩ : LargeEvenLabel) hΛX hq h3dvd hcon
        hhX hperf
      omega
    obtain ⟨k, hk⟩ := h3dvd
    omega
  dsimp only at hcore
  rcases hcore with ⟨a, ds, hsum, hne, hlen, hmem, hbr⟩ | ⟨-, -, hbr⟩
  · have hlen12 : ds.length = 1 ∨ ds.length = 2 := by
      have hpos : 0 < ds.length := List.length_pos_iff.mpr hne
      have h3 : ds.length < 3 := hlen
      omega
    rcases hq with ⟨rfl, hdq⟩ | ⟨rfl, hdq⟩
    ·
      have hds1 : ∀ x ∈ ds, x = 1 := by
        intro x hx
        rcases hmem x hx with h1 | ⟨hbad, -, -⟩
        · exact h1
        · exact absurd hbad (by simp)
      have hsum_eq : ds.sum = ds.length := by
        simpa using List.sum_eq_length_nsmul ds 1 hds1
      rcases hbr with ⟨hΛ', hh'⟩ | ⟨hbad, -, -⟩
      · have hiso : GGLabelIso (⟨.A, a - 1, nX⟩ : LargeEvenLabel) labJ :=
          hrig _ _ _ hΛ' hΛJ hh' hhJ
        have hT' : ggResLineJLabel T (⟨.A, a - 1, nX⟩ : LargeEvenLabel) :=
          ggResLineJLabel_of_iso_symm hT hiso
        have hrank' : a - 1 = 2 ∨ a - 1 = 3 :=
          ggResLineJLabel_rank_of_three_dvd_sub hT' hdq
        have ha : a = 3 ∨ a = 4 := by
          have h1 : 1 ≤ a - 1 := hΛ'.2.1
          rcases hrank' with h | h <;> omega
        rcases ha with rfl | rfl
        · exfalso
          rcases hlen12 with h | h <;> omega
        · have hrX : rX = 5 := by
            rcases hN with h | h <;> omega
          subst hrX
          refine ⟨⟨.A, 3, nX⟩, ⟨.A, 5, nX⟩, ?_, hΛX, ggTablePRow_line_A3 nX hdq, ?_,
            hhX⟩
          · simpa using hΛ'
          · simpa using hh'
      · exact absurd hbad (by simp)
    ·
      rcases hbr with ⟨hΛ', hh'⟩ | ⟨-, rfl, hΛ', hh'⟩
      · have hiso : GGLabelIso (⟨.twA, a - 1, nX⟩ : LargeEvenLabel) labJ :=
          hrig _ _ _ hΛ' hΛJ hh' hhJ
        have hT' : ggResLineJLabel T (⟨.twA, a - 1, nX⟩ : LargeEvenLabel) :=
          ggResLineJLabel_of_iso_symm hT hiso
        have hrank' : a - 1 = 2 ∨ a - 1 = 3 :=
          ggResLineJLabel_rank_of_three_dvd_add hT' hdq
        have ha : a = 3 ∨ a = 4 := by
          have h1 : 2 ≤ a - 1 := hΛ'.2.1
          rcases hrank' with h | h <;> omega
        rcases ha with rfl | rfl
        · have hn2 : 2 ≤ nX := hΛ'.2.2 rfl
          have hds1 : ∀ x ∈ ds, x = 1 := by
            intro x hx
            rcases hmem x hx with h1 | ⟨-, hbad, -⟩
            · exact h1
            · exact absurd hbad (by omega)
          have hsum_eq : ds.sum = ds.length := by
            simpa using List.sum_eq_length_nsmul ds 1 hds1
          exfalso
          rcases hlen12 with h | h <;> omega
        · have hrX : rX = 5 := by
            rcases hN with h | h <;> omega
          subst hrX
          refine ⟨⟨.twA, 3, nX⟩, ⟨.twA, 5, nX⟩, ?_, hΛX,
            ggTablePRow_line_twA3 nX hdq, ?_, hhX⟩
          · simpa using hΛ'
          · simpa using hh'
      · have hiso : GGLabelIso (⟨.A, 1, nX⟩ : LargeEvenLabel) labJ :=
          hrig _ _ _ hΛ' hΛJ hh' hhJ
        have hT' : ggResLineJLabel T (⟨.A, 1, nX⟩ : LargeEvenLabel) :=
          ggResLineJLabel_of_iso_symm hT hiso
        exact absurd (Or.inl ⟨rfl, rfl⟩ : GGTPNRankOne (⟨.A, 1, nX⟩ : LargeEvenLabel))
          (ggResLineJLabel_not_rankOne hT')
  ·
    rcases hbr with ⟨-, hΛ', hh'⟩ | ⟨-, hge3, hΛ', hh'⟩
    · rcases hN with hN3 | hN6
      · rw [hN3] at hΛ'
        simp [LargeEvenInLambda2] at hΛ'
      · have hb : (rX + 1) / 3 = 2 := by rw [hN6]
        have hΛ'' : LargeEvenInLambda2 (⟨.A, 1, 3 * nX⟩ : LargeEvenLabel) := by
          simpa [hb] using hΛ'
        have hh'' : GGHasLabel (⟨.A, 1, 3 * nX⟩ : LargeEvenLabel)
            (↥J ⧸ Subgroup.center ↥J) := by simpa [hb] using hh'
        have hiso : GGLabelIso (⟨.A, 1, 3 * nX⟩ : LargeEvenLabel) labJ :=
          hrig _ _ _ hΛ'' hΛJ hh'' hhJ
        exact absurd (Or.inl ⟨rfl, rfl⟩ : GGTPNRankOne (⟨.A, 1, 3 * nX⟩ : LargeEvenLabel))
          (ggResLineJLabel_not_rankOne (ggResLineJLabel_of_iso_symm hT hiso))
    · exfalso
      rcases hN with h | h
      · rw [h] at hge3
        norm_num at hge3
      · rw [h] at hge3
        norm_num at hge3

end CFSG.StandardType

end
