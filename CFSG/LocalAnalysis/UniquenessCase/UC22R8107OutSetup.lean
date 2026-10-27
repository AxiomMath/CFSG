module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Case
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107OutCase
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107U3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

private theorem mem_uniqueSet_of_zpowers {M L A : Subgroup G} {a : G} (hL : L ∈ calC M)
    (hr : CFSG.Open.pRank 3 L = 1) (haL : a ∈ L) (ha3 : orderOf a = 3)
    (hU : zpowers a ∈ uniqueSet M) (hAL : A ≤ L) (hA : Nat.card A = 3) : A ∈ uniqueSet M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hh, rfl⟩ := RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime hr.le
    (zpowers_le.2 haL) hAL (by rw [Nat.card_zpowers, ha3]) hA
  exact PartTwo.conj_mem_uniqueSet hU (hL.1.le hh)

theorem r8107_dataOfSetup (hSE : StronglyEmbeddedFive) (hKThin : KThinSimple)
    (hS : RankThreeUC.Standing G) (S : RankThreeUC.Setup G)
    (hSg : UC6S846.SigmaStd (dataOfSetup hS S)) (h82 : F08.R82 (dataOfSetup hS S))
    (h847 : R8107E3.R847OrderThree (dataOfSetup hS S)) (h76 : F07.R76Sig (dataOfSetup hS S))
    (h614 : UC6.R6_14 (dataOfSetup hS S)) : F08.R8107 (dataOfSetup hS S) := by
  intro L₁ hL₁ L₂ hL₂ h12 r₁ r₂ hs₁ hs₂ A₁ A₂ hA₁ hc₁ hA₂ hc₂
  by_cases hsp : IsStronglyPEmbedded 3 (dataOfSetup hS S).M
  · exact ⟨R8107Thin.mem_uniqueSet_of_card_three hsp hL₁ hA₁ hc₁,
      R8107Thin.mem_uniqueSet_of_card_three hsp hL₂ hA₂ hc₂⟩
  obtain ⟨hZ₁, hloss₁⟩ := R8107U3.center_and_loss _ hKThin hL₁ r₁ hs₁
  obtain ⟨hZ₂, hloss₂⟩ := R8107U3.center_and_loss _ hKThin hL₂ r₂ hs₂
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hp3 : p ≠ 3 := by have := R8107E3.five_le_of_mem_sig hSg hsp hL₁ hp; omega
  obtain ⟨R, hR, a₁, ha₁, a₂, ha₂, ho₁, ho₂, y, -, hy, hy₁, hy₂⟩ :=
    R8107E3.exists_pair_mem_sig hSg h82 hsp hL₁ hL₂ h12 r₁ r₂ hloss₁ hloss₂ hp
  have hc₁3 : Nat.card (zpowers a₁) = 3 := by rw [Nat.card_zpowers, ho₁]
  have hc₂3 : Nat.card (zpowers a₂) = 3 := by rw [Nat.card_zpowers, ho₂]
  have hodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR.isPGroup
    exact hn ▸ Odd.pow (by decide)
  have hR₁ := R8107Odd.le_normalizer_of_odd h82 hsp hL₁ r₁ hR.le hodd
  have hR₂ := R8107Odd.le_normalizer_of_odd h82 hsp hL₂ r₂ hR.le hodd
  have hM3 := R8107E3.pRank_three_le_three_of_not_sp hSg hsp hL₁
  have hsh : ∀ {L : Subgroup G}, L ∈ calC (dataOfSetup hS S).M → CFSG.Open.pRank 3 L = 1 →
      (F08.Thin8 L ∨ ∃ n : ℕ, IsU3 (Bar2 L) n) →
      R8107Shape.ThinShape (Bar2 L) ∨ ∃ n : ℕ, IsU3 (Bar2 L) n := fun hL r hs =>
    hs.imp_left fun s => R8107Shape.thinShape_of_thin8 _ hKThin hL s
      (R8107Shape.three_dvd_card_bar2 r)
  have hN₁ := h847 L₁ hL₁ r₁ _ (zpowers_le.2 ha₁.1) hc₁3 p hp hp3 hs₁
  have hN₂ := h847 L₂ hL₂ r₂ _ (zpowers_le.2 ha₂.1) hc₂3 p hp hp3 hs₂
  have hyc : y ∈ centralizer ((zpowers a₁ ⊔ zpowers a₂ : Subgroup G) : Set G) := by
    rw [← zpowers_le, le_centralizer_iff]
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_) <;> rw [mem_centralizer_iff] <;>
      rintro _ ⟨k, rfl⟩
    exacts [((show Commute y a₁ from hy₁).zpow_left k).eq,
      ((show Commute y a₂ from hy₂).zpow_left k).eq]
  have hN₁₂ := R8107E3.normalizer_le_of_le_of_r847 hSg h847 hp hp3 hL₁ r₁ hs₁
    (zpowers_le.2 ha₁.1) hc₁3 le_sup_left hy hyc
  have hU : zpowers a₁ ∈ uniqueSet (dataOfSetup hS S).M ∧
      zpowers a₂ ∈ uniqueSet (dataOfSetup hS S).M := by
    by_cases hI₁ : R8107E3.CubesInner R L₁
    · by_cases hI₂ : R8107E3.CubesInner R L₂
      · exact R8107E3.mem_uniqueSet_of_cubesInner hSE hS S hSg h82 h847 h76 h614 hsp hL₁ hL₂ h12
          r₁ r₂ hs₁ hs₂ hZ₁ hZ₂ hloss₁ hloss₂ hR hI₁ hI₂ ha₁ ha₂ ho₁ ho₂ hp hy hy₁ hy₂
      · obtain ⟨a₀, ha₀, ha₀3, hout⟩ := R8107E3.exists_not_isInnerAut_of_not_cubesInner hR₂ hI₂
        exact (mem_uniqueSet_of_outer h82 hsp hL₂ hL₁ h12.symm r₂ r₁ (hsh hL₂ r₂ hs₂)
          (hsh hL₁ r₁ hs₁) hZ₂ hZ₁ hM3 hR hR₂ ⟨ha₂.2, ha₂.1⟩ ⟨ha₁.2, ha₁.1⟩ ho₂ ho₁ hN₂ hN₁
          (by rwa [sup_comm]) ha₀ ha₀3 hout).symm
    · obtain ⟨a₀, ha₀, ha₀3, hout⟩ := R8107E3.exists_not_isInnerAut_of_not_cubesInner hR₁ hI₁
      exact mem_uniqueSet_of_outer h82 hsp hL₁ hL₂ h12 r₁ r₂ (hsh hL₁ r₁ hs₁) (hsh hL₂ r₂ hs₂)
        hZ₁ hZ₂ hM3 hR hR₁ ⟨ha₁.2, ha₁.1⟩ ⟨ha₂.2, ha₂.1⟩ ho₁ ho₂ hN₁ hN₂ hN₁₂ ha₀ ha₀3 hout
  exact ⟨mem_uniqueSet_of_zpowers hL₁ r₁ ha₁.1 ho₁ hU.1 hA₁ hc₁,
    mem_uniqueSet_of_zpowers hL₂ r₂ ha₂.1 ho₂ hU.2 hA₂ hc₂⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out
