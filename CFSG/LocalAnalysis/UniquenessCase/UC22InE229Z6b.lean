module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z6
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5U3
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z34
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThreeStrong
import CFSG.LocalAnalysis.UniquenessCase.UC7P3NoBad
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl1
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_normalizer_le_of_involution (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : Sec7Core4.KIDExcluded k) (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXM : X ≤ k.M) {B₁ : Subgroup G} (hB₁M : B₁ ≤ k.M)
    (hB₁ : IsElemAbelian k.p B₁) (hB₁c : Nat.card B₁ = k.p ^ 2)
    (hB₁X : B₁ ≤ centralizer (X : Set G)) {Y : Subgroup G} (hYM : Y ≤ k.M)
    (hB₁Y : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 k.M) {t : G}
    (ht : t ∈ Y ⊓ normalizer (X : Set G)) (ht2 : orderOf t = 2) :
    normalizer (X : Set G) ≤ k.M := by
  rcases uc22ine229_normalizer_le_or_inf_eq_bot k h5 hno hSE hX hXM hB₁M hB₁ hB₁c hB₁X with
    h | hQ
  · exact h
  by_contra hnot
  have hB₁N : B₁ ≤ normalizer (X : Set G) :=
    hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hH := k.config_normalizer hX hXM
    (CFSG.SectionRank.le_pRank k.prime.one_lt (le_inf hB₁M hB₁N) hB₁ hB₁c) hnot
  have htC := uc22ine229_le_centralizer hQ hB₁X hB₁Y ht
  have h75 := k.step75 h5 hSE
  exact k.false_of_involution h75 hH (k.goodZ_of_kIDExcluded h5 hno hH hSEZ h75).1
    (le_inf hB₁N hB₁M) hB₁ hB₁c ⟨ht.2, hYM ht.1⟩ ht2
    fun a ha => (Subgroup.mem_centralizer_iff.1 htC) a ha

theorem uc22ine229_kIDExcluded_setup4 (hB3 : BadNoStrongThree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) {p : ℕ}
    (hp : p ∈ uniqueFourSigma S.M) (hp5 : 5 ≤ p) (hsp : IsStronglyPEmbedded p S.M) :
    Sec7Core4.KIDExcluded (Sec7Core4.ofUnique hS hU S.M S.maxLocal p hp hsp) := by
  by_cases h3 : 3 ∈ uniqueFourBeta G
  · exact Sec7Core4.kIDExcluded_of_strongThree _ hp5
      (isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h3) hB3
  · exact Sec7Core4.kIDExcluded_of_not_mem_beta _ h3

theorem uc22ine229_normalizer_le_of_isSU3_setup4 (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hB3 : BadNoStrongThree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hgr : GriessAllModelsStatement)
    (hC : uc22pwCartanSU3) {p : ℕ} (hp : p ∈ (UC6.dataOfSetup4 hS hU S).sig) (hp5 : 5 ≤ p)
    {Y : Subgroup G} (hY : Y ∈ calC (UC6.dataOfSetup4 hS hU S).M) {n : ℕ}
    (hYn : IsSU3 (Bar2 Y) n) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1)
    {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) :
    normalizer (X : Set G) ≤ (UC6.dataOfSetup4 hS hU S).M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  by_cases hqs : q ∈ (UC6.dataOfSetup4 hS hU S).sig
  · exact uc22ine229_normalizer_le_of_mem_sig hSg hY hqs hXY hX1 hXq
  have hrank := uc22ine229_pRank_le_three hSg hq hq2 hqs
  have hpP : p.Prime := ((UC6.dataOfSetup4 hS hU S).sig_prime p hp).1
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := uc22ine229_exists_B₁_of_isSU3
    (UCK.u3SylOmega_of_griess hgr) hY hYn hpP hp5
    (UC6.opRes_eq_of_stronglyEmbedded_uc6 hS.simple hS.nonab hpP hsp)
    (UC6.four_le_pRank_of_sigma hp) hXY hq hq2 hXc
    (uc22ine229_not_dvd_card_center hgr hYn hq hq2 hqn) hrank
  obtain ⟨t, ht, ht2⟩ := uc22ine229_exists_involution_of_isSU3 hgr hC hY hYn hq hq2 hqn hXY hXc
  exact uc22ine229_normalizer_le_of_involution (.ofUnique hS hU S.M S.maxLocal p hp hsp) hp5
    (uc22ine229_kIDExcluded_setup4 hB3 hS hU S hσ hp hp5 hsp) hSE hSEZ hX1 (hXY.trans hY.1.le)
    hB₁M hB₁ hB₁c hB₁X hY.1.le hB₁Y ht ht2

end CFSG.LocalAnalysis.UniquenessCase.UC22
