module

import CFSG.RankThree.PartOne.K128.D4Syl
import CFSG.RankThree.PartOne.K128.SylowShapeRank
import CFSG.RankThree.PartOne.K133.G2Odd
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem exists_dvd_phiNat_of_dvd_pow_six_sub_one {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (h : p ∣ q ^ 6 - 1) :
    ∃ m, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) ∧
      p ∣ CFSG.RankThree.PartOne.K128.phiNat m q := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
  have hfac : q ^ 6 - 1 =
      (q - 1) * ((q + 1) * ((q ^ 2 + q + 1) * (q ^ 2 - q + 1))) := by
    zify [hq1, hq2, hq6]
    ring
  rw [hfac] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · exact ⟨1, Or.inl rfl, by simpa [CFSG.RankThree.PartOne.K128.phiNat] using h1⟩
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · exact ⟨2, Or.inr (Or.inl rfl), by simpa [CFSG.RankThree.PartOne.K128.phiNat] using h2⟩
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)),
      by simpa [CFSG.RankThree.PartOne.K128.phiNat] using h3⟩
  · exact ⟨6, Or.inr (Or.inr (Or.inr rfl)),
      by simpa [CFSG.RankThree.PartOne.K128.phiNat] using h3⟩

private theorem phiNat_ne_zero {m q : ℕ} (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) (hq : 2 ≤ q) :
    CFSG.RankThree.PartOne.K128.phiNat m q ≠ 0 := by
  rcases hm with rfl | rfl | rfl | rfl
  · simp only [CFSG.RankThree.PartOne.K128.phiNat]
    omega
  · simp only [CFSG.RankThree.PartOne.K128.phiNat]
    omega
  · simp only [CFSG.RankThree.PartOne.K128.phiNat]
    positivity
  · simp only [CFSG.RankThree.PartOne.K128.phiNat]
    have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    omega

private theorem two_le_open_pRank_of_sylowShape {X : Type} [Group X] [Finite X] {p e : ℕ}
    (hp : p.Prime) (he : 1 ≤ e)
    (h : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e X) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p X]
  exact CFSG.RankThree.PartOne.K1214.two_le_pRank_of_sylowShape_sq hp he h


private theorem open_pRank_le_two_of_sylowShape {X : Type} [Group X] [Finite X] {p e : ℕ}
    (hp : p.Prime) (h : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e X) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  exact CFSG.RankThree.PartOne.K133.card_le_sq_of_sylowShape hp h E
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE)

theorem pRank_d4_eq_two {X : Type} [Group X] [Finite X] {n : ℕ} (h : Is3D4 X n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ 2 ^ (6 * n) - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup X) = 2 := by
  obtain ⟨hadm, hmod⟩ :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (t := .trialityD4) (by decide)).1 h).2
  have hn : 1 ≤ n := hadm.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card
      (G := X) (t := CFSG.Blueprint.Chevalley.TwistTag.D4) (p := 2) (f := n)
      Nat.prime_two hn hmod
  have hK3 : Nat.card K = (2 ^ n) ^ 3 := by
    simpa [CFSG.Blueprint.Chevalley.TwistTag.order] using hK
  have hq2 : 2 ≤ 2 ^ n := by
    have hn0 : n ≠ 0 := by omega
    simpa using Nat.le_self_pow hn0 2
  have hq6 : (2 ^ n) ^ 6 = 2 ^ (6 * n) := by
    rw [← pow_mul, Nat.mul_comm]
  have hdvd : p ∣ (2 ^ n) ^ 6 - 1 := by
    rwa [hq6]
  obtain ⟨m, hm, hdphi⟩ := exists_dvd_phiNat_of_dvd_pow_six_sub_one hp hq2 hdvd
  have ht : 1 ≤ (CFSG.RankThree.PartOne.K128.phiNat m (2 ^ n)).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp (phiNat_ne_zero hm hq2) hdphi
  have hshapeC : CFSG.RankThree.PartOne.K1214.SylowShape p 2
      ((CFSG.RankThree.PartOne.K128.phiNat m (2 ^ n)).factorization p)
      (CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K
        σ.toRingHom) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.RankThree.PartOne.K128.sylowShape_D4 (ℓ := 2) (f := n) hn K hK3 σ hσ hm
      hp hp5 hdphi
  have hshapeX : CFSG.RankThree.PartOne.K1214.SylowShape p 2
      ((CFSG.RankThree.PartOne.K128.phiNat m (2 ^ n)).factorization p) X :=
    CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv e hshapeC
  exact le_antisymm (open_pRank_le_two_of_sylowShape hp hshapeX)
    (two_le_open_pRank_of_sylowShape hp ht hshapeX)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core
