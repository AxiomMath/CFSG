module

public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_one_of_r6_6 {D : Data G} (h66 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_6 D)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M ∨ p ∈ D.sig) {N : Subgroup G}
    (hN : N ∈ calMOf D.T) (hNM : N ≠ D.M) : CFSG.Open.pRank p N ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ CFSG.Open.pRank p N := by omega
  exact hNM ((h66 p hp hp2).1 hpM N hN h2)

theorem pRank_three_eq_three_of_sig {D : Data G} (hx : DataExt D) (hsig : D.sig = {3})
    (he3 : CFSG.Open.evenRank G = 3) : CFSG.Open.pRank 3 D.M = 3 := by
  have hle : CFSG.Open.pRank 3 D.M ≤ 3 := by
    have h := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by decide) D.M D.maxLocal.1
    omega
  have hge : 3 ≤ CFSG.Open.pRank 3 D.M := hx.three_le 3 (by simp [hsig])
  omega

theorem mem_uniqueSet_of_r846 {D : Data G} (h846 : F08.R846 D) {Y : Subgroup G} {n : ℕ}
    (hY : Y ∈ calC D.M) (hSU3 : IsSU3 (Bar2 Y) n) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrdvd : r ∣ 2 ^ n + 1) {A : Subgroup G} (hAY : A ≤ Y) (hA : Nat.card A = r) :
    A ∈ uniqueSet D.M := by
  have hAM : A ≤ D.M := hAY.trans (CFSG.Open.IsSubnormal.le hY.1)
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA
    exact hr.ne_one hA.symm
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rwa [pow_one])
  exact mem_uniqueSet_of_isStronglyPEmbedded hr (h846 Y hY n hSU3 r hr hr3 hrdvd) hAM hAne hAp

omit [Finite G] in
theorem not_conjClosure_le_of_mem_uniqueSet {M N A : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hN : CFSG.Open.rankThreeIsMaxTwoLocal N)
    (hAU : A ∈ uniqueSet M) (hNM : N ≠ M) : ¬ conjClosure N A ≤ M := by
  intro hHle
  have hHmem : conjClosure N A ∈ uniqueSet M :=
    mem_uniqueSet_of_le hAU (uc22p22v_le_conjClosure N A) hHle
  have hNH : N ≤ normalizer (conjClosure N A : Set G) :=
    uc22p22v_le_normalizer_conjClosure N A
  have hNle : N ≤ M := hNH.trans (normalizer_le_of_mem_uniqueSet hM hHmem)
  exact hNM (hN.2 M hM.1 hNle).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
