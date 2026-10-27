module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePTorus
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGALocalRank
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggDelUClRA_twoLocalRank_le {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} (d : ℕ) (hAbA : Ab ≤ A) (hrank : GGTPNRank 3 X Ab)
    (hnum : GGTPNNum 3 (3 ^ (d + 1)) A Ab) :
    LargeEvenTwoLocalRank 3 X ≤ d + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) := by
  obtain ⟨hnum1, -⟩ := hnum
  have hpow : (3 : ℕ) ^ (d + 1) = 3 * 3 ^ d := by rw [pow_succ]; ring
  rw [hpow] at hnum1
  have hcardA : Nat.card A ≤ 3 ^ d := Nat.le_of_mul_le_mul_left hnum1 (by norm_num)
  have hcardAb : Nat.card Ab ≤ 3 ^ d := (Subgroup.card_le_of_le hAbA).trans hcardA
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hmd : m ≤ d := by
    rw [hmcard] at hcardAb
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcardAb
  omega

private theorem ggDelUClRA_sum_pos {ds : List ℕ} (hne : ds ≠ [])
    (hmem : ∀ x ∈ ds, x = 1 ∨ x = 2 ∨ x = 3) : 1 ≤ ds.sum := by
  have hpos : 0 < ds.sum := by
    rw [List.sum_pos_iff_exists_pos_nat]
    rcases ds with _ | ⟨x, ds⟩
    · exact absurd rfl hne
    · refine ⟨x, by simp, ?_⟩
      rcases hmem x (by simp) with rfl | rfl | rfl <;> norm_num
  omega

private theorem ggDelUClRA_row_succ (d : ℕ) (hd : 5 ≤ d) :
    GGTablePRow 3 (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) (⟨.twA, d, 1⟩ : LargeEvenLabel) := by
  unfold GGTablePRow
  right; right; right; right; right; right; right; left
  refine ⟨rfl, by norm_num, ?_, Or.inl ?_⟩
  · show 2 ≤ d - 1
    omega
  · show (⟨.twA, d, 1⟩ : LargeEvenLabel) = ⟨.twA, d - 1 + 1, 1⟩
    rw [show d - 1 + 1 = d by omega]

private theorem ggDelUClRA_row_succ_succ (d : ℕ) (hd : 5 ≤ d) (hd3 : 3 ∣ d + 2) :
    GGTablePRow 3 (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) (⟨.twA, d + 1, 1⟩ : LargeEvenLabel) := by
  unfold GGTablePRow
  right; right; right; right; right; right; right; left
  refine ⟨rfl, by norm_num, ?_, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
  · show 2 ≤ d - 1
    omega
  · show (⟨.twA, d + 1, 1⟩ : LargeEvenLabel) = ⟨.twA, d - 1 + 2, 1⟩
    rw [show d - 1 + 2 = d + 1 by omega]
  · show 3 ∣ d - 1 + 3
    rw [show d - 1 + 3 = d + 2 by omega]
    exact hd3

theorem ggDelUClRARK_holds :
    GGTablePKnownRK fun p n labJ labX =>
      GGRegimeDeletedUnitary1836 p n labJ labX ∧ GGKacRA labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨rfl, d, hd5, hn, hlabJ⟩, hRA⟩ := hr
  obtain ⟨⟨hloc, hflat, -, hrank, hnum, hself, honly, hm⟩, -⟩ := hd
  obtain ⟨hAb, -, -, -⟩ := hflat
  rcases labJ with ⟨tJ, rJ, m⟩
  simp only [LargeEvenLabel.mk.injEq] at hlabJ
  obtain ⟨rfl, rfl, rfl⟩ := hlabJ
  subst hn
  rcases labX with ⟨tX, rX, nX⟩
  have hperf : commutator X = ⊤ := by
    have hm0 := hm
    unfold GGTPNMarked at hm0
    exact hm0.1
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hm' : GGTPNMarked 3 (fun _ lab => lab = (⟨tX, rX, nX⟩ : LargeEvenLabel)) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  have hcore := split_or_fieldType_of_ggKacRA Nat.prime_three hloc honly hRA hm'
  have hcut := ggDelUClRA_twoLocalRank_le d hAb hrank hnum
  have h3dvd : 3 ∣ rX + 1 := by
    rcases hRA with ⟨-, hd, -⟩ | ⟨-, hd, -⟩
    · exact hd
    · exact hd
  have hq : (tX = .A ∧ 3 ∣ 2 ^ nX - 1) ∨ (tX = .twA ∧ 3 ∣ 2 ^ nX + 1) := by
    rcases hRA with ⟨ht, -, hq⟩ | ⟨ht, -, hq⟩
    · exact Or.inl ⟨ht, hq⟩
    · exact Or.inr ⟨ht, hq⟩
  dsimp only at hcore
  rcases hcore with ⟨a, ds, hsum, hne, hlen, hmem, hbr⟩ | ⟨-, -, hbr⟩
  ·
    have hmem13 : ∀ x ∈ ds, x = 1 ∨ x = 2 ∨ x = 3 := by
      intro x hx
      rcases hmem x hx with h1 | ⟨-, -, h1⟩
      · exact Or.inl h1
      · exact Or.inr h1
    have hs1 : 1 ≤ ds.sum := ggDelUClRA_sum_pos hne hmem13
    rcases hbr with ⟨hΛ', hh'⟩ | ⟨hAg, ha2, hΛ', hh'⟩
    · have hiso : GGLabelIso (⟨tX, a - 1, nX⟩ : LargeEvenLabel)
          (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) := hrig _ _ _ hΛ' hΛJ hh' hhJ
      have heq := ggLabelIso_twA_right (r := d - 1) (by omega) hiso
      have htX : tX = .twA := congrArg LargeEvenLabel.tag heq
      have hra : a - 1 = d - 1 := congrArg LargeEvenLabel.rank heq
      have hnX : nX = 1 := congrArg LargeEvenLabel.n heq
      have ha : a = d := by omega
      subst htX
      subst hnX
      by_cases hs1 : ds.sum = 1
      · have hrX : rX = d := by omega
        subst rX
        exact ⟨⟨.twA, d - 1, 1⟩, ⟨.twA, d, 1⟩, hΛJ, hΛX,
          ggDelUClRA_row_succ d hd5, hhJ, hhX⟩
      have hN7 : 7 ≤ rX + 1 := by omega
      have hN9 : 9 ≤ rX + 1 := by
        obtain ⟨k, hk⟩ := h3dvd
        omega
      have hcut3 := ggALocalRankSubThree_holds X (⟨.twA, rX, 1⟩ : LargeEvenLabel) hΛX hq
        h3dvd hN9 hhX hperf
      obtain ⟨mrank, hmcard, hmrank⟩ := hrank
      have hmN : rX + 1 - 3 ≤ mrank := Nat.le_of_add_le_add_right (hcut3.trans hmrank)
      have hcardA : Nat.card A ≤ 3 ^ d := by
        have hnum1 := hnum.1
        have hpow : (3 : ℕ) ^ (d + 1) = 3 * 3 ^ d := by rw [pow_succ]; ring
        rw [hpow] at hnum1
        exact Nat.le_of_mul_le_mul_left hnum1 (by norm_num)
      have hcardA_ge : 3 ^ (rX + 1 - 3) ≤ Nat.card A := by
        calc 3 ^ (rX + 1 - 3) ≤ 3 ^ mrank :=
              (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mpr hmN
          _ = Nat.card Ab := hmcard.symm
          _ ≤ Nat.card A := Subgroup.card_le_of_le hAb
      have hbig : 3 ^ ((rX + 1) / 3 + 1) < Nat.card A := by
        have hlt : (rX + 1) / 3 + 1 < rX + 1 - 3 := by omega
        have hpowlt : 3 ^ ((rX + 1) / 3 + 1) < 3 ^ (rX + 1 - 3) :=
          (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mpr hlt
        exact hpowlt.trans_le hcardA_ge
      have htorus := ggDelU_torus_le_card hloc.1 hself hm hperf hN9 h3dvd
        (by simpa using hhX) hbig
      have hNle : rX + 1 ≤ d + 2 := by
        have h1 : 3 ^ (rX + 1 - 2) ≤ 3 ^ d := htorus.trans hcardA
        have h2 : rX + 1 - 2 ≤ d :=
          (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
        omega
      have hrX : rX = d + 1 := by omega
      subst rX
      have hd3 : 3 ∣ d + 2 := by simpa using h3dvd
      exact ⟨⟨.twA, d - 1, 1⟩, ⟨.twA, d + 1, 1⟩, hΛJ, hΛX,
        ggDelUClRA_row_succ_succ d hd5 hd3, hhJ, hhX⟩
    ·
      have hiso : GGLabelIso (⟨.A, 1, nX⟩ : LargeEvenLabel)
          (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) := hrig _ _ _ hΛ' hΛJ hh' hhJ
      have heq := ggLabelIso_twA_right (r := d - 1) (by omega) hiso
      have ht : LargeEvenLieTag.A = LargeEvenLieTag.twA := congrArg LargeEvenLabel.tag heq
      cases ht
  ·
    rcases hbr with ⟨-, hΛ', hh'⟩ | ⟨-, -, hΛ', hh'⟩
    · have hiso : GGLabelIso (⟨.A, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel)
          (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) := hrig _ _ _ hΛ' hΛJ hh' hhJ
      have heq := ggLabelIso_twA_right (r := d - 1) (by omega) hiso
      have ht : LargeEvenLieTag.A = LargeEvenLieTag.twA := congrArg LargeEvenLabel.tag heq
      cases ht
    · have hiso : GGLabelIso (⟨.twA, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel)
          (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) := hrig _ _ _ hΛ' hΛJ hh' hhJ
      have heq := ggLabelIso_twA_right (r := d - 1) (by omega) hiso
      have hn3 : 3 * nX = 1 := congrArg LargeEvenLabel.n heq
      omega

end CFSG.StandardType

end
