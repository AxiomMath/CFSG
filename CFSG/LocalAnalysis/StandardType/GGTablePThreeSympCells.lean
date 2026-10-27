module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSympDefs
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
import CFSG.RankThree.PartOne.S12K.OrdRigidL

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem one_le_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = 2 ^ n) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst hn0
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [h] at h2
  norm_num at h2

private theorem one_le_n_of_lambda2 {lab : LargeEvenLabel} (h : LargeEvenInLambda2 lab) :
    1 ≤ lab.n := by
  have h' := h
  simp only [LargeEvenInLambda2] at h'
  exact h'.1

private theorem two_pow_dvd_360_le {k : ℕ} (h : 2 ^ k ∣ 360) : k ≤ 3 := by
  by_contra hk
  have h4 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
  exact absurd (h4.trans h) (by decide)

private theorem sympCell_label {X : Type} [Group X] {J : Subgroup X} {P : LargeEvenMarkProp J}
    (hJ : LargeEvenMarking J P) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : J ⧸ Subgroup.center J ≃* R),
      LargeEvenInLambda2 lab ∧ P lab R I F θ ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) ∧
      LargeEvenRawDatum lab (fun R _ _ _ => Nat.card R = Nat.card (J ⧸ Subgroup.center J)) := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hJ
  obtain ⟨R, hR, I, F, hsimple, hnonab, θ, hP⟩ := largeEvenRawDatum_exists hraw
  refine ⟨lab, R, hR, I, F, θ, hlab, hP, ?_, ?_⟩
  · exact largeEvenRawDatum_mono (fun R' _ _ _ hQ => ⟨hQ.2.2.choose⟩) hraw
  · exact largeEvenRawDatum_mono
      (fun R' _ _ _ hQ => (Nat.card_congr hQ.2.2.choose.toEquiv).symm) hraw

private theorem one_le_n_of_ggHasLabel_A {N : Type} [Group N] {r n : ℕ}
    (h : GGHasLabel (⟨.A, r, n⟩ : LargeEvenLabel) N) : 1 ≤ n := by
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  exact one_le_of_card_eq_two_pow hKcard

private theorem one_le_n_of_ggHasLabel_C {N : Type} [Group N] {r n : ℕ}
    (h : GGHasLabel (⟨.C, r, n⟩ : LargeEvenLabel) N) : 1 ≤ n := by
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  exact one_le_of_card_eq_two_pow hKcard

private theorem two_le_of_three_dvd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n)
    (h : 3 ∣ 2 ^ n - 1) : 2 ≤ n := by
  by_contra hlt
  have hn1 : n = 1 := by omega
  subst hn1
  norm_num at h

private theorem lambda2_A_of {a n : ℕ} (ha : 2 ≤ a) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n - 1) :
    LargeEvenInLambda2 (⟨.A, a - 1, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, by omega, fun _ => two_le_of_three_dvd_two_pow_sub_one hn h3⟩

private theorem lambda2_twA_of {a : ℕ} (ha : 4 ≤ a) :
    LargeEvenInLambda2 (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨le_rfl, by omega, fun h => by omega⟩

private theorem lambda2_C_of {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n)
    (hne : ¬ (s = 2 ∧ n = 1)) : LargeEvenInLambda2 (⟨.C, s, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  refine ⟨hn, hs, ?_⟩
  intro hs2
  have : n ≠ 1 := fun hn1 => hne ⟨hs2, hn1⟩
  omega

private theorem labOrd_ne_360_of_g2 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGLabelG2 lab) : SporadicShape.labOrd lab ≠ 360 := by
  obtain ⟨t, l, n⟩ := lab
  rcases h with ht | ht
  · have ht' : t = .G2 := by simpa using ht
    subst ht'
    have hn2 : 2 ≤ n := by
      have h' := hlab
      simp only [LargeEvenInLambda2] at h'
      exact h'.2.2
    have hl : CFSG.EvenSmallLie.CatalogOrders.lieExp
        (markTag (⟨.G2, l, n⟩ : LargeEvenLabel))
        (markRank (⟨.G2, l, n⟩ : LargeEvenLabel)) = 6 := by
      norm_num [CFSG.EvenSmallLie.CatalogOrders.lieExp, markTag, markRank]
    intro h360
    have hpow : (2 ^ n) ^ (CFSG.EvenSmallLie.CatalogOrders.lieExp
        (markTag (⟨.G2, l, n⟩ : LargeEvenLabel))
        (markRank (⟨.G2, l, n⟩ : LargeEvenLabel))) ∣
        SporadicShape.labOrd (⟨.G2, l, n⟩ : LargeEvenLabel) := by
      simpa only [SporadicShape.labOrd, markTag, markRank, markChar, markDeg] using
        (CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .G2) (n := 0) (by decide)
          (2 ^ n))
    have hdvd : (2 ^ n) ^ 6 ∣ 360 := by
      have h := h360 ▸ hpow
      simpa only [hl] using h
    have hdvd' : 2 ^ (n * 6) ∣ 360 := by simpa only [pow_mul] using hdvd
    have := two_pow_dvd_360_le hdvd'
    omega
  · have ht' : t = .G2der := by simpa using ht
    subst ht'
    have hl : CFSG.EvenSmallLie.CatalogOrders.lieExp
        (markTag (⟨.G2der, l, n⟩ : LargeEvenLabel))
        (markRank (⟨.G2der, l, n⟩ : LargeEvenLabel)) = 3 := by
      norm_num [CFSG.EvenSmallLie.CatalogOrders.lieExp, markTag, markRank]
    intro h360
    have hpow : (3 ^ 1) ^ (CFSG.EvenSmallLie.CatalogOrders.lieExp
        (markTag (⟨.G2der, l, n⟩ : LargeEvenLabel))
        (markRank (⟨.G2der, l, n⟩ : LargeEvenLabel))) ∣
        SporadicShape.labOrd (⟨.G2der, l, n⟩ : LargeEvenLabel) := by
      simpa only [SporadicShape.labOrd, markTag, markRank, markChar, markDeg] using
        (CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSU) (n := 3) (by decide) (3 ^ 1))
    have hdvd : 3 ^ 3 ∣ 360 := by
      have h := h360 ▸ hpow
      simpa only [hl, pow_one] using h
    exact absurd hdvd (by decide)

private theorem labOrd_ne_360_of_a2 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGLabelA2 lab) : SporadicShape.labOrd lab ≠ 360 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hrank, hn2, htag⟩ := h
  have hrank' : l = 2 := by simpa using hrank
  have hn : 2 ≤ n := by simpa using hn2
  have htag' : (t = .A ∧ 3 ∣ 2 ^ n - 1) ∨ (t = .twA ∧ 3 ∣ 2 ^ n + 1) := by
    simpa using htag
  rcases htag' with ⟨ht, -⟩ | ⟨ht, -⟩
  · subst ht
    subst hrank'
    have hl : CFSG.EvenSmallLie.CatalogOrders.lieExp
        (markTag (⟨.A, 2, n⟩ : LargeEvenLabel))
        (markRank (⟨.A, 2, n⟩ : LargeEvenLabel)) = 3 := by
      norm_num [CFSG.EvenSmallLie.CatalogOrders.lieExp, markTag, markRank]
    intro h360
    have hpow : (2 ^ n) ^ (CFSG.EvenSmallLie.CatalogOrders.lieExp
        (markTag (⟨.A, 2, n⟩ : LargeEvenLabel))
        (markRank (⟨.A, 2, n⟩ : LargeEvenLabel))) ∣
        SporadicShape.labOrd (⟨.A, 2, n⟩ : LargeEvenLabel) := by
      simpa only [SporadicShape.labOrd, markTag, markRank, markChar, markDeg] using
        (CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSL) (n := 3) (by decide) (2 ^ n))
    have hdvd : (2 ^ n) ^ 3 ∣ 360 := by
      have h := h360 ▸ hpow
      simpa only [hl] using h
    have hdvd' : 2 ^ (n * 3) ∣ 360 := by simpa only [pow_mul] using hdvd
    have := two_pow_dvd_360_le hdvd'
    omega
  · subst ht
    subst hrank'
    have hl : CFSG.EvenSmallLie.CatalogOrders.lieExp
        (markTag (⟨.twA, 2, n⟩ : LargeEvenLabel))
        (markRank (⟨.twA, 2, n⟩ : LargeEvenLabel)) = 3 := by
      norm_num [CFSG.EvenSmallLie.CatalogOrders.lieExp, markTag, markRank]
    intro h360
    have hpow : (2 ^ n) ^ (CFSG.EvenSmallLie.CatalogOrders.lieExp
        (markTag (⟨.twA, 2, n⟩ : LargeEvenLabel))
        (markRank (⟨.twA, 2, n⟩ : LargeEvenLabel))) ∣
        SporadicShape.labOrd (⟨.twA, 2, n⟩ : LargeEvenLabel) := by
      simpa only [SporadicShape.labOrd, markTag, markRank, markChar, markDeg] using
        (CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSU) (n := 3) (by decide) (2 ^ n))
    have hdvd : (2 ^ n) ^ 3 ∣ 360 := by
      have h := h360 ▸ hpow
      simpa only [hl] using h
    have hdvd' : 2 ^ (n * 3) ∣ 360 := by simpa only [pow_mul] using hdvd
    have := two_pow_dvd_360_le hdvd'
    omega

private theorem labOrd_ne_360_of_triD4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .triD4) : SporadicShape.labOrd lab ≠ 360 := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .triD4 := by simpa using h
  subst ht
  have hn : 1 ≤ n := one_le_n_of_lambda2 hlab
  have hl : CFSG.EvenSmallLie.CatalogOrders.lieExp
      (markTag (⟨.triD4, l, n⟩ : LargeEvenLabel))
      (markRank (⟨.triD4, l, n⟩ : LargeEvenLabel)) = 12 := by
    norm_num [CFSG.EvenSmallLie.CatalogOrders.lieExp, markTag, markRank]
  intro h360
  have hpow : (2 ^ n) ^ (CFSG.EvenSmallLie.CatalogOrders.lieExp
      (markTag (⟨.triD4, l, n⟩ : LargeEvenLabel))
      (markRank (⟨.triD4, l, n⟩ : LargeEvenLabel))) ∣
      SporadicShape.labOrd (⟨.triD4, l, n⟩ : LargeEvenLabel) := by
    simpa only [SporadicShape.labOrd, markTag, markRank, markChar, markDeg] using
      (CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .trialityD4) (n := 0) (by decide)
        (2 ^ n))
  have hdvd : (2 ^ n) ^ 12 ∣ 360 := by
    have h := h360 ▸ hpow
    simpa only [hl] using h
  have hdvd' : 2 ^ (n * 12) ∣ 360 := by simpa only [pow_mul] using hdvd
  have := two_pow_dvd_360_le hdvd'
  omega

private theorem labOrd_ne_360_of_D4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .D ∧ lab.rank = 4) : SporadicShape.labOrd lab ≠ 360 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl⟩ := h
  have ht' : t = .D := by simpa using ht
  have hl' : l = 4 := by simpa using hl
  subst ht'
  subst hl'
  have hn : 1 ≤ n := one_le_n_of_lambda2 hlab
  have htagD : markTag (⟨.D, 4, n⟩ : LargeEvenLabel) = .POmegaPlus := by simp [markTag]
  have hrankD : markRank (⟨.D, 4, n⟩ : LargeEvenLabel) = 4 := by simp [markRank]
  have hl : CFSG.EvenSmallLie.CatalogOrders.lieExp
      (markTag (⟨.D, 4, n⟩ : LargeEvenLabel))
      (markRank (⟨.D, 4, n⟩ : LargeEvenLabel)) = 12 := by
    rw [htagD, hrankD]
    norm_num [CFSG.EvenSmallLie.CatalogOrders.lieExp]
  have hlabOrd : SporadicShape.labOrd (⟨.D, 4, n⟩ : LargeEvenLabel) =
      CFSG.EvenSmallLie.CatalogOrders.lieOrd .POmegaPlus 4 (2 ^ n) := by
    simp only [SporadicShape.labOrd, markChar, markDeg, htagD, hrankD]
  intro h360
  have hpow : (2 ^ n) ^ (CFSG.EvenSmallLie.CatalogOrders.lieExp
      (markTag (⟨.D, 4, n⟩ : LargeEvenLabel))
      (markRank (⟨.D, 4, n⟩ : LargeEvenLabel))) ∣
      SporadicShape.labOrd (⟨.D, 4, n⟩ : LargeEvenLabel) := by
    rw [hlabOrd, htagD, hrankD]
    exact CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .POmegaPlus) (n := 4) (by decide)
      (2 ^ n)
  have hdvd : (2 ^ n) ^ 12 ∣ 360 := by
    have h := h360 ▸ hpow
    simpa only [hl] using h
  have hdvd' : 2 ^ (n * 12) ∣ 360 := by simpa only [pow_mul] using hdvd
  have := two_pow_dvd_360_le hdvd'
  omega

private theorem labOrd_ne_360_of_A1 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∧ lab.rank = 1) : SporadicShape.labOrd lab ≠ 360 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl⟩ := h
  have ht' : t = .A := by simpa using ht
  have hl' : l = 1 := by simpa using hl
  subst ht'
  subst hl'
  have hn2 : 2 ≤ n := by
    have h' := hlab
    simp only [LargeEvenInLambda2] at h'
    exact h'.2.2 trivial
  have hl : CFSG.EvenSmallLie.CatalogOrders.lieExp
      (markTag (⟨.A, 1, n⟩ : LargeEvenLabel))
      (markRank (⟨.A, 1, n⟩ : LargeEvenLabel)) = 1 := by
    norm_num [CFSG.EvenSmallLie.CatalogOrders.lieExp, markTag, markRank]
  have hform : SporadicShape.labOrd (⟨.A, 1, n⟩ : LargeEvenLabel) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    CFSG.RankThree.PartOne.S12K.ordA_one_eq (g := n) (by omega)
  intro h360
  have hpow : (2 ^ n) ^ (CFSG.EvenSmallLie.CatalogOrders.lieExp
      (markTag (⟨.A, 1, n⟩ : LargeEvenLabel))
      (markRank (⟨.A, 1, n⟩ : LargeEvenLabel))) ∣
      SporadicShape.labOrd (⟨.A, 1, n⟩ : LargeEvenLabel) := by
    simpa only [SporadicShape.labOrd, markTag, markRank, markChar, markDeg] using
      (CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSL) (n := 2) (by decide) (2 ^ n))
  have hdvd : 2 ^ n ∣ 360 := by
    have h := h360 ▸ hpow
    simpa only [hl, pow_one] using h
  have hle : n ≤ 3 := two_pow_dvd_360_le hdvd
  rcases (by omega : n = 2 ∨ n = 3) with rfl | rfl
  · have hval : SporadicShape.labOrd (⟨.A, 1, 2⟩ : LargeEvenLabel) = 60 := by
      rw [hform]; norm_num
    omega
  · have hval : SporadicShape.labOrd (⟨.A, 1, 3⟩ : LargeEvenLabel) = 504 := by
      rw [hform]; norm_num
    omega

private theorem false_of_A2_tag {lab : LargeEvenLabel} {t : LargeEvenLieTag}
    (hA2 : GGLabelA2 lab) (ht : lab.tag = t) (htA : t ≠ .A) (httwA : t ≠ .twA) : False := by
  have h' : lab.tag = .A ∨ lab.tag = .twA := by
    rcases hA2.2.2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases h' with h | h
  · exact htA (ht ▸ h)
  · exact httwA (ht ▸ h)

private theorem not_ggLabelIso_of_GGLabelG2 {lab L : LargeEvenLabel} (h : GGLabelG2 lab)
    (hL : L.tag = .A ∨ L.tag = .twA ∨ L.tag = .C) : ¬ GGLabelIso lab L := by
  rcases h with ht | ht
  · intro hiso
    rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨-, h8⟩
    · have : L.tag = .G2 := by rw [← h1]; exact ht
      rcases hL with hL | hL | hL <;> rw [hL] at this <;> exact absurd this (by simp)
    · rcases h2 with h2 | h2 <;> rw [ht] at h2 <;> exact absurd h2 (by simp)
    · rw [h3] at ht; exact absurd ht (by simp)
    · rw [h4] at ht; exact absurd ht (by simp)
    · rw [h5] at ht; exact absurd ht (by simp)
    · rw [h6] at ht; exact absurd ht (by simp)
    · rw [h7] at ht; exact absurd ht (by simp)
    · rw [h8] at ht; exact absurd ht (by simp)
  · intro hiso
    rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨-, h8⟩
    · have : L.tag = .G2der := by rw [← h1]; exact ht
      rcases hL with hL | hL | hL <;> rw [hL] at this <;> exact absurd this (by simp)
    · rcases h2 with h2 | h2 <;> rw [ht] at h2 <;> exact absurd h2 (by simp)
    · rw [h3] at ht; exact absurd ht (by simp)
    · rw [h4] at ht; exact absurd ht (by simp)
    · rw [h5] at ht; exact absurd ht (by simp)
    · rw [h6] at ht; exact absurd ht (by simp)
    · rw [h7] at ht; exact absurd ht (by simp)
    · rw [h8] at ht; exact absurd ht (by simp)

private theorem not_ggLabelIso_of_A2_twA {lab : LargeEvenLabel} {a : ℕ}
    (hA2 : GGLabelA2 lab) (ha : 4 ≤ a) :
    ¬ GGLabelIso lab (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) := by
  have hrank : lab.rank = 2 := hA2.1
  intro hiso
  rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨-, h8⟩
  · have : lab.rank = a - 1 := by rw [h1]
    omega
  · rcases h2 with h2 | h2
    · exact false_of_A2_tag hA2 h2 (by simp) (by simp)
    · exact false_of_A2_tag hA2 h2 (by simp) (by simp)
  · have ht : lab.tag = .D := by rw [h3]
    exact false_of_A2_tag hA2 ht (by simp) (by simp)
  · rw [h4] at hrank; norm_num at hrank
  · have ht : lab.tag = .twD := by rw [h5]
    exact false_of_A2_tag hA2 ht (by simp) (by simp)
  · rw [h6] at hrank; norm_num at hrank
  · have ht : lab.tag = .twD := by rw [h7]
    exact false_of_A2_tag hA2 ht (by simp) (by simp)
  · rw [h8] at hrank; norm_num at hrank

private theorem not_ggLabelIso_of_A2_C {lab : LargeEvenLabel} {s n : ℕ}
    (hA2 : GGLabelA2 lab) : ¬ GGLabelIso lab (⟨.C, s, n⟩ : LargeEvenLabel) := by
  have hrank : lab.rank = 2 := hA2.1
  intro hiso
  rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩
  · have ht : lab.tag = .C := by rw [h1]
    exact false_of_A2_tag hA2 ht (by simp) (by simp)
  · rcases h2 with h2 | h2
    · exact false_of_A2_tag hA2 h2 (by simp) (by simp)
    · exact false_of_A2_tag hA2 h2 (by simp) (by simp)
  · have ht : lab.tag = .D := by rw [h3]
    exact false_of_A2_tag hA2 ht (by simp) (by simp)
  · rw [h4] at hrank; norm_num at hrank
  · have ht : lab.tag = .twD := by rw [h5]
    exact false_of_A2_tag hA2 ht (by simp) (by simp)
  · rw [h6] at hrank; norm_num at hrank
  · have ht : lab.tag = .twD := by rw [h7]
    exact false_of_A2_tag hA2 ht (by simp) (by simp)
  · have : (⟨.C, s, n⟩ : LargeEvenLabel).tag = .twD := by rw [h8]
    exact absurd this (by simp)

private theorem not_ggLabelIso_of_twA_rank2 {lab L : LargeEvenLabel}
    (htwA : lab.tag = .twA) (hrank : lab.rank = 2)
    (hLtag : L.tag = .A ∨ L.tag = .twA ∨ L.tag = .C)
    (hLrank : L.tag = .twA → 3 ≤ L.rank) : ¬ GGLabelIso lab L := by
  intro hiso
  rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨-, h8⟩
  · rcases hLtag with hL | hL | hL
    · have : L.tag = .twA := by rw [← h1]; exact htwA
      rw [hL] at this; exact absurd this (by simp)
    · have : 3 ≤ lab.rank := by rw [h1]; exact hLrank hL
      omega
    · have : L.tag = .twA := by rw [← h1]; exact htwA
      rw [hL] at this; exact absurd this (by simp)
  · rcases h2 with h2 | h2 <;> rw [htwA] at h2 <;> exact absurd h2 (by simp)
  · rw [h3] at htwA; exact absurd htwA (by simp)
  · rw [h4] at htwA; exact absurd htwA (by simp)
  · rw [h5] at htwA; exact absurd htwA (by simp)
  · rw [h6] at hrank; norm_num at hrank
  · rw [h7] at htwA; exact absurd htwA (by simp)
  · rw [h8] at htwA; exact absurd htwA (by simp)

private theorem not_ggLabelIso_of_tag_triD4 {lab L : LargeEvenLabel} (htag : lab.tag = .triD4)
    (hL : L.tag = .A ∨ L.tag = .twA ∨ L.tag = .C) : ¬ GGLabelIso lab L := by
  intro hiso
  rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨-, h8⟩
  · have : L.tag = .triD4 := by rw [← h1]; exact htag
    rcases hL with hL | hL | hL <;> rw [hL] at this <;> exact absurd this (by simp)
  · rcases h2 with h2 | h2 <;> rw [htag] at h2 <;> exact absurd h2 (by simp)
  · rw [h3] at htag; exact absurd htag (by simp)
  · rw [h4] at htag; exact absurd htag (by simp)
  · rw [h5] at htag; exact absurd htag (by simp)
  · rw [h6] at htag; exact absurd htag (by simp)
  · rw [h7] at htag; exact absurd htag (by simp)
  · rw [h8] at htag; exact absurd htag (by simp)

private theorem not_ggLabelIso_of_D_rank4 {lab L : LargeEvenLabel}
    (htag : lab.tag = .D) (hrank : lab.rank = 4)
    (hL : L.tag = .A ∨ L.tag = .twA ∨ L.tag = .C) : ¬ GGLabelIso lab L := by
  intro hiso
  rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨-, h8⟩
  · have : L.tag = .D := by rw [← h1]; exact htag
    rcases hL with hL | hL | hL <;> rw [hL] at this <;> exact absurd this (by simp)
  · rcases h2 with h2 | h2 <;> rw [htag] at h2 <;> exact absurd h2 (by simp)
  · rw [h3] at hrank; norm_num at hrank
  · rw [h4] at htag; exact absurd htag (by simp)
  · rw [h5] at htag; exact absurd htag (by simp)
  · rw [h6] at htag; exact absurd htag (by simp)
  · rw [h7] at htag; exact absurd htag (by simp)
  · rw [h8] at htag; exact absurd htag (by simp)

private theorem not_ggLabelIso_of_A1 {lab L : LargeEvenLabel}
    (htag : lab.tag = .A) (hrank : lab.rank = 1)
    (hLtagA : L.tag ≠ .A) (hLtwD : L.tag ≠ .twD) : ¬ GGLabelIso lab L := by
  intro hiso
  rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩
  · have : L.tag = .A := by rw [← h1]; exact htag
    exact hLtagA this
  · rcases h2 with h2 | h2 <;> rw [htag] at h2 <;> exact absurd h2 (by simp)
  · rw [h3] at htag; exact absurd htag (by simp)
  · rw [h4] at hrank; norm_num at hrank
  · rw [h5] at htag; exact absurd htag (by simp)
  · rw [h6] at htag; exact absurd htag (by simp)
  · rw [h7] at htag; exact absurd htag (by simp)
  · have : L.tag = .twD := by rw [h8]
    exact hLtwD this

private theorem eq_three_of_iso_A2 {lab : LargeEvenLabel} {a n : ℕ}
    (hA2 : GGLabelA2 lab) (hiso : GGLabelIso lab (⟨.A, a - 1, n⟩ : LargeEvenLabel)) : a = 3 := by
  have hrank : lab.rank = 2 := hA2.1
  rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨-, h8⟩
  · have : lab.rank = a - 1 := by rw [h1]
    omega
  · rcases h2 with h2 | h2
    · exact (false_of_A2_tag hA2 h2 (by simp) (by simp)).elim
    · exact (false_of_A2_tag hA2 h2 (by simp) (by simp)).elim
  · have ht : lab.tag = .D := by rw [h3]
    exact (false_of_A2_tag hA2 ht (by simp) (by simp)).elim
  · rw [h4] at hrank; norm_num at hrank
  · have ht : lab.tag = .twD := by rw [h5]
    exact (false_of_A2_tag hA2 ht (by simp) (by simp)).elim
  · rw [h6] at hrank; norm_num at hrank
  · have ht : lab.tag = .twD := by rw [h7]
    exact (false_of_A2_tag hA2 ht (by simp) (by simp)).elim
  · rw [h8] at hrank; norm_num at hrank

private theorem eq_two_of_iso_A1 {lab : LargeEvenLabel} {a n : ℕ}
    (htag : lab.tag = .A) (hrank : lab.rank = 1)
    (hiso : GGLabelIso lab (⟨.A, a - 1, n⟩ : LargeEvenLabel)) : a = 2 := by
  rcases hiso with h1 | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩
  · have : lab.rank = a - 1 := by rw [h1]
    omega
  · rcases h2 with h2 | h2 <;> rw [htag] at h2 <;> exact absurd h2 (by simp)
  · rw [h3] at htag; exact absurd htag (by simp)
  · rw [h4] at hrank; norm_num at hrank
  · rw [h5] at htag; exact absurd htag (by simp)
  · rw [h6] at htag; exact absurd htag (by simp)
  · rw [h7] at htag; exact absurd htag (by simp)
  · have : (⟨.A, a - 1, n⟩ : LargeEvenLabel).tag = .twD := by rw [h8]
    exact absurd this (by simp)

theorem sympCell_noG2
    {X : Type} [Group X] {n : ℕ} {A : Subgroup (MulAut X)} {J : Subgroup X}
    (hS : SympShapeConcl n A J) : ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab) := by
  intro hJ
  obtain ⟨lab, R, hR, I, F, θ, hlab, hP, hGG, hrawN⟩ := sympCell_label hJ
  have hG2 : GGLabelG2 lab := hP
  rcases hS with ⟨a, ha2, h3, hL, hZ, hcardA⟩ | ⟨hn1, a, ha4, hL⟩ | ⟨s, hs2, hne, hL⟩ |
    ⟨hn1, hcard⟩
  · have hLlab : LargeEvenInLambda2 (⟨.A, a - 1, n⟩ : LargeEvenLabel) :=
      lambda2_A_of ha2 (one_le_n_of_ggHasLabel_A hL) h3
    exact not_ggLabelIso_of_GGLabelG2 hG2 (Or.inl rfl)
      (ggLabelRigidInput_holds lab ⟨.A, a - 1, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) := lambda2_twA_of ha4
    exact not_ggLabelIso_of_GGLabelG2 hG2 (Or.inr (Or.inl rfl))
      (ggLabelRigidInput_holds lab ⟨.twA, a - 1, 1⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.C, s, n⟩ : LargeEvenLabel) :=
      lambda2_C_of hs2 (one_le_n_of_ggHasLabel_C hL) hne
    exact not_ggLabelIso_of_GGLabelG2 hG2 (Or.inr (Or.inr rfl))
      (ggLabelRigidInput_holds lab ⟨.C, s, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hlab360 : SporadicShape.labOrd lab = 360 := by
      rw [SporadicShape.labOrd_eq_of_rawDatum hlab hrawN, hcard]
    exact (labOrd_ne_360_of_g2 hlab hG2) hlab360

theorem sympCell_noA2
    {X : Type} [Group X] {n : ℕ} {A : Subgroup (MulAut X)} {J : Subgroup X}
    (hS : SympShapeConcl n A J) (hJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab)) :
    Subgroup.center J ≠ ⊥ := by
  obtain ⟨lab, R, hR, I, F, θ, hlab, hP, hGG, hrawN⟩ := sympCell_label hJ
  have hA2 : GGLabelA2 lab := hP
  rcases hS with ⟨a, ha2, h3, hL, hZ, hcardA⟩ | ⟨hn1, a, ha4, hL⟩ | ⟨s, hs2, hne, hL⟩ |
    ⟨hn1, hcard⟩
  · have hLlab : LargeEvenInLambda2 (⟨.A, a - 1, n⟩ : LargeEvenLabel) :=
      lambda2_A_of ha2 (one_le_n_of_ggHasLabel_A hL) h3
    have hiso := ggLabelRigidInput_holds lab ⟨.A, a - 1, n⟩ (J ⧸ Subgroup.center J) hlab hLlab
      hGG hL
    exact hZ (eq_three_of_iso_A2 hA2 hiso)
  · have hLlab : LargeEvenInLambda2 (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) := lambda2_twA_of ha4
    exact absurd
      (ggLabelRigidInput_holds lab ⟨.twA, a - 1, 1⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
      (not_ggLabelIso_of_A2_twA hA2 ha4)
  · have hLlab : LargeEvenInLambda2 (⟨.C, s, n⟩ : LargeEvenLabel) :=
      lambda2_C_of hs2 (one_le_n_of_ggHasLabel_C hL) hne
    exact absurd (ggLabelRigidInput_holds lab ⟨.C, s, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
      (not_ggLabelIso_of_A2_C hA2)
  · have hlab360 : SporadicShape.labOrd lab = 360 := by
      rw [SporadicShape.labOrd_eq_of_rawDatum hlab hrawN, hcard]
    exact absurd hlab360 (labOrd_ne_360_of_a2 hlab hA2)

theorem sympCell_noTwA2
    {X : Type} [Group X] {n : ℕ} {A : Subgroup (MulAut X)} {J : Subgroup X}
    (hS : SympShapeConcl n A J) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) := by
  intro hJ
  obtain ⟨lab, R, hR, I, F, θ, hlab, hP, hGG, hrawN⟩ := sympCell_label hJ
  obtain ⟨hA2, htwA⟩ := hP
  have hrank : lab.rank = 2 := hA2.1
  rcases hS with ⟨a, ha2, h3, hL, hZ, hcardA⟩ | ⟨hn1, a, ha4, hL⟩ | ⟨s, hs2, hne, hL⟩ |
    ⟨hn1, hcard⟩
  · have hLlab : LargeEvenInLambda2 (⟨.A, a - 1, n⟩ : LargeEvenLabel) :=
      lambda2_A_of ha2 (one_le_n_of_ggHasLabel_A hL) h3
    exact not_ggLabelIso_of_twA_rank2 htwA hrank (Or.inl rfl) (fun h => absurd h (by simp))
      (ggLabelRigidInput_holds lab ⟨.A, a - 1, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) := lambda2_twA_of ha4
    exact not_ggLabelIso_of_twA_rank2 htwA hrank (Or.inr (Or.inl rfl))
      (fun _ => by show 3 ≤ a - 1; omega)
      (ggLabelRigidInput_holds lab ⟨.twA, a - 1, 1⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.C, s, n⟩ : LargeEvenLabel) :=
      lambda2_C_of hs2 (one_le_n_of_ggHasLabel_C hL) hne
    exact not_ggLabelIso_of_twA_rank2 htwA hrank (Or.inr (Or.inr rfl))
      (fun h => absurd h (by simp))
      (ggLabelRigidInput_holds lab ⟨.C, s, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hlab360 : SporadicShape.labOrd lab = 360 := by
      rw [SporadicShape.labOrd_eq_of_rawDatum hlab hrawN, hcard]
    exact absurd hlab360 (labOrd_ne_360_of_a2 hlab hA2)

theorem sympCell_noTriD4
    {X : Type} [Group X] {n : ℕ} {A : Subgroup (MulAut X)} {J : Subgroup X}
    (hS : SympShapeConcl n A J) : ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4) := by
  intro hJ
  obtain ⟨lab, R, hR, I, F, θ, hlab, hP, hGG, hrawN⟩ := sympCell_label hJ
  have htri : lab.tag = .triD4 := hP
  rcases hS with ⟨a, ha2, h3, hL, hZ, hcardA⟩ | ⟨hn1, a, ha4, hL⟩ | ⟨s, hs2, hne, hL⟩ |
    ⟨hn1, hcard⟩
  · have hLlab : LargeEvenInLambda2 (⟨.A, a - 1, n⟩ : LargeEvenLabel) :=
      lambda2_A_of ha2 (one_le_n_of_ggHasLabel_A hL) h3
    exact not_ggLabelIso_of_tag_triD4 htri (Or.inl rfl)
      (ggLabelRigidInput_holds lab ⟨.A, a - 1, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) := lambda2_twA_of ha4
    exact not_ggLabelIso_of_tag_triD4 htri (Or.inr (Or.inl rfl))
      (ggLabelRigidInput_holds lab ⟨.twA, a - 1, 1⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.C, s, n⟩ : LargeEvenLabel) :=
      lambda2_C_of hs2 (one_le_n_of_ggHasLabel_C hL) hne
    exact not_ggLabelIso_of_tag_triD4 htri (Or.inr (Or.inr rfl))
      (ggLabelRigidInput_holds lab ⟨.C, s, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hlab360 : SporadicShape.labOrd lab = 360 := by
      rw [SporadicShape.labOrd_eq_of_rawDatum hlab hrawN, hcard]
    exact absurd hlab360 (labOrd_ne_360_of_triD4 hlab htri)

theorem sympCell_noD4Odd
    {X : Type} [Group X] {n : ℕ} {A : Subgroup (MulAut X)} {J : Subgroup X}
    (hS : SympShapeConcl n A J) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n) := by
  intro hJ
  obtain ⟨lab, R, hR, I, F, θ, hlab, hP, hGG, hrawN⟩ := sympCell_label hJ
  obtain ⟨hDtag, hDrank, hDodd⟩ := hP
  rcases hS with ⟨a, ha2, h3, hL, hZ, hcardA⟩ | ⟨hn1, a, ha4, hL⟩ | ⟨s, hs2, hne, hL⟩ |
    ⟨hn1, hcard⟩
  · have hLlab : LargeEvenInLambda2 (⟨.A, a - 1, n⟩ : LargeEvenLabel) :=
      lambda2_A_of ha2 (one_le_n_of_ggHasLabel_A hL) h3
    exact not_ggLabelIso_of_D_rank4 hDtag hDrank (Or.inl rfl)
      (ggLabelRigidInput_holds lab ⟨.A, a - 1, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) := lambda2_twA_of ha4
    exact not_ggLabelIso_of_D_rank4 hDtag hDrank (Or.inr (Or.inl rfl))
      (ggLabelRigidInput_holds lab ⟨.twA, a - 1, 1⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.C, s, n⟩ : LargeEvenLabel) :=
      lambda2_C_of hs2 (one_le_n_of_ggHasLabel_C hL) hne
    exact not_ggLabelIso_of_D_rank4 hDtag hDrank (Or.inr (Or.inr rfl))
      (ggLabelRigidInput_holds lab ⟨.C, s, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hlab360 : SporadicShape.labOrd lab = 360 := by
      rw [SporadicShape.labOrd_eq_of_rawDatum hlab hrawN, hcard]
    exact absurd hlab360 (labOrd_ne_360_of_D4 hlab ⟨hDtag, hDrank⟩)

theorem sympCell_noA1
    {X : Type} [Group X] {n : ℕ} {A : Subgroup (MulAut X)} {J : Subgroup X}
    (hS : SympShapeConcl n A J) (hA : 3 ^ 3 ≤ Nat.card A) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) := by
  intro hJ
  obtain ⟨lab, R, hR, I, F, θ, hlab, hP, hGG, hrawN⟩ := sympCell_label hJ
  obtain ⟨hAtag, hArank⟩ := hP
  rcases hS with ⟨a, ha2, h3, hL, hZ, hcardA⟩ | ⟨hn1, a, ha4, hL⟩ | ⟨s, hs2, hne, hL⟩ |
    ⟨hn1, hcard⟩
  · have hLlab : LargeEvenInLambda2 (⟨.A, a - 1, n⟩ : LargeEvenLabel) :=
      lambda2_A_of ha2 (one_le_n_of_ggHasLabel_A hL) h3
    have hiso := ggLabelRigidInput_holds lab ⟨.A, a - 1, n⟩ (J ⧸ Subgroup.center J) hlab hLlab
      hGG hL
    exact absurd (hcardA (eq_two_of_iso_A1 hAtag hArank hiso)) (by omega)
  · have hLlab : LargeEvenInLambda2 (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) := lambda2_twA_of ha4
    exact not_ggLabelIso_of_A1 hAtag hArank (by simp) (by simp)
      (ggLabelRigidInput_holds lab ⟨.twA, a - 1, 1⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hLlab : LargeEvenInLambda2 (⟨.C, s, n⟩ : LargeEvenLabel) :=
      lambda2_C_of hs2 (one_le_n_of_ggHasLabel_C hL) hne
    exact not_ggLabelIso_of_A1 hAtag hArank (by simp) (by simp)
      (ggLabelRigidInput_holds lab ⟨.C, s, n⟩ (J ⧸ Subgroup.center J) hlab hLlab hGG hL)
  · have hlab360 : SporadicShape.labOrd lab = 360 := by
      rw [SporadicShape.labOrd_eq_of_rawDatum hlab hrawN, hcard]
    exact absurd hlab360 (labOrd_ne_360_of_A1 hlab ⟨hAtag, hArank⟩)

end CFSG.StandardType.TablePThreeKG

end
