module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Res
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5U3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229B13
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Invol
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_normalizer_le_of_isSU3_three_setup4 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3) (hres : L34GFResidueAt hS hU S)
    (hp : 3 ∈ (UC6.dataOfSetup4 hS hU S).sig) {Y : Subgroup G}
    (hY : Y ∈ calC (UC6.dataOfSetup4 hS hU S).M) {n : ℕ} (hYn : IsSU3 (Bar2 Y) n) {q : ℕ}
    (hq : q.Prime) (hq5 : 5 ≤ q) (hqn : q ∣ 2 ^ n - 1) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) :
    normalizer (X : Set G) ≤ (UC6.dataOfSetup4 hS hU S).M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have hq2 : q ≠ 2 := by omega
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  by_cases hqs : q ∈ (UC6.dataOfSetup4 hS hU S).sig
  · exact uc22ine229_normalizer_le_of_mem_sig hSg hY hqs hXY hX1 hXq
  have hrank := uc22ine229_pRank_le_three hSg hq hq2 hqs
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  have h4 := UC6.four_le_pRank_of_sigma hp
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := uc22ine229_exists_B₁_three_of_isSU3 hgr
    UCK.u3ThreeRank hY hYn
    (UC6.opRes_eq_of_stronglyEmbedded_uc6 hS.simple hS.nonab Nat.prime_three hsp) h4 hXY hq hq5
    hXc (uc22ine229_not_dvd_card_center hgr hYn hq hq2 hqn) hrank
  obtain ⟨t, ht, ht2⟩ := uc22ine229_exists_involution_of_isSU3 hgr hC hY hYn hq hq2 hqn hXY hXc
  exact uc22ine229_normalizer_le_of_involution_three hG3 hRee hK3
    (.ofUnique hS hU S.M S.maxLocal 3 hp hsp) (hres hp hsp) rfl h4 hY hq hq5 hXY hXc hrank
    (Or.inr ⟨n, hYn, hqn⟩) hB₁M hB₁ hB₁c hB₁X hB₁Y ht ht2

end CFSG.LocalAnalysis.UniquenessCase.UC22
