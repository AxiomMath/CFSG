module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920Slices
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2EvenStrong
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R920L2Even (D : Data G) : Prop :=
  ∀ (L D₃ : Subgroup G) (n : ℕ), L ∈ calC D.M → D₃ ≤ L → Nat.card D₃ = 3 →
    D₃ ∈ uniqueSet D.M → IsL2 (Bar2 L) n → Even n → IsStronglyPEmbedded 3 D.M →
    UniqueMax D.M L ∨ IsAlt (Bar2 L) 5

@[expose] def R920L2Three (D : Data G) : Prop :=
  ∀ (L D₃ A : Subgroup G), L ∈ calC D.M → D₃ ≤ L → Nat.card D₃ = 3 → D₃ ∈ uniqueSet D.M →
    IsL2 (Bar2 L) 3 → A ∈ uniqueSet D.M → A ≤ L → (Nat.card A).Prime →
    Nat.card A ∣ 2 ^ 3 - 1 → (∃ p ∈ D.sig, p ∣ 2 ^ 3 + 1) → UniqueMax D.M L

@[expose] def R920L2Rest (D : Data G) : Prop :=
  ∀ (L D₃ : Subgroup G) (n : ℕ), L ∈ calC D.M → D₃ ≤ L → Nat.card D₃ = 3 →
    D₃ ∈ uniqueSet D.M → IsL2 (Bar2 L) n →
    (∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set G) ≤ D.M) →
    (∃ p ∈ D.sig, p ∣ Nat.card L) →
    ((Odd n ∧ 5 ≤ n ∧ (∃ A : Subgroup G, A ∈ uniqueSet D.M ∧ A ≤ L ∧ (Nat.card A).Prime ∧
        Nat.card A ∣ 2 ^ n - 1) ∧ ∃ p ∈ D.sig, p ∣ 2 ^ n + 1) ∨
      (Even n ∧ ¬ IsStronglyPEmbedded 3 D.M)) →
    UniqueMax D.M L ∨ IsAlt (Bar2 L) 5

theorem r920L2E_of_parts (D : Data G) (hev : R920L2Even D) (h3 : R920L2Three D)
    (hrest : R920L2Rest D) : R920L2E D := by
  intro L D₃ n hL hD₃L hD₃ hD₃U hL2 hN hσ hcond
  rcases Nat.even_or_odd n with hevn | hodd
  · by_cases hsp : IsStronglyPEmbedded 3 D.M
    · exact hev L D₃ n hL hD₃L hD₃ hD₃U hL2 hevn hsp
    · exact hrest L D₃ n hL hD₃L hD₃ hD₃U hL2 hN hσ (Or.inr ⟨hevn, hsp⟩)
  · rcases hcond with hevn | ⟨⟨A, hAU, hAL, hAp, hAdvd⟩, hp⟩
    · exact absurd hevn (Nat.not_even_iff_odd.mpr hodd)
    · have hn2 : 2 ≤ n := uc22p20g_two_le_of_isL2 hL2
      have hcase : n = 3 ∨ 5 ≤ n := by
        obtain ⟨k, hk⟩ := hodd
        omega
      rcases hcase with rfl | hn5
      · exact Or.inl (h3 L D₃ A hL hD₃L hD₃ hD₃U hL2 hAU hAL hAp hAdvd hp)
      · exact hrest L D₃ n hL hD₃L hD₃ hD₃U hL2 hN hσ
          (Or.inl ⟨hodd, hn5, ⟨A, hAU, hAL, hAp, hAdvd⟩, hp⟩)

theorem r920L2Three_of_inputs (D : Data G) (h61 : UC6.R6_1 D)
    (h63c : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore) (h640 : UC6.R6_40_1 D)
    (hK32 : UCK.K32) (hK46 : UCK.K46Semireg) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    R920L2Three D := by
  intro L D₃ A hL hD₃L hD₃ hD₃U hL2 hAU hAL hAp hAdvd hp
  have h3 : 3 ∈ D.sig := by
    obtain ⟨p, hpσ, hpd⟩ := hp
    have hpp : p.Prime := (D.sig_prime p hpσ).1
    have h9 : (2 : ℕ) ^ 3 + 1 = 3 ^ 2 := by norm_num
    rw [h9] at hpd
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1
      (hpp.dvd_of_dvd_pow hpd)
    exact hp3 ▸ hpσ
  have hA7 : Nat.card A = 7 := by
    have h7 : (2 : ℕ) ^ 3 - 1 = 7 := by norm_num
    rw [h7] at hAdvd
    exact (Nat.prime_dvd_prime_iff_eq hAp (by norm_num)).1 hAdvd
  exact s16h_e3_R920L28_of_inputs D h61 h63c h640 hK32 hK46 hSch h3 L D₃ A hL hL.1.le hL2
    (pCoreOf_ne_bot_of_mem_calC D.standing.charTwo D.maxLocal.1 hL) hD₃L hD₃ hD₃U hAL hA7 hAU

theorem r920L2Even_of_inputs
    (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (D : Data G)
    (h63 : UC6.R6_3 D) (h912 : F09.R912L2 D) (hR92 : F09.R92 D) : R920L2Even D := by
  intro L D₃ n hL hD₃L hD₃ hD₃U hL2 hev hsp
  by_cases hU : UniqueMax D.M L
  · exact Or.inl hU
  obtain ⟨m, rfl⟩ := hev
  have hm2 : 2 ≤ m + m := uc22p20g_two_le_of_isL2 hL2
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  · exfalso
    have hL2' : IsL2 (Bar2 L) (2 * m) := by rwa [two_mul]
    rcases uniqueMax_or_mem_calY2_of_sp D h63 hsp hL hL2 with h | h
    · exact hU h
    · exact false_of_mem_calY2_of_isL2_even hK462 hSch D h912 hR92 hL hm1 hL2' h
  · have hm : m = 1 := by omega
    subst hm
    exact Or.inr (isAlt_five_of_isL2_two hL2)

theorem r920L2Even_dataOfSetup
    (hK462 : UCK.K462) (hK32 : UCK.K32)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (h63c : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore)
    (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G) (S : CFSG.LocalAnalysis.RankThreeUC.Setup G)
    (h63 : UC6.R6_3 (Three.dataOfSetup hS S)) (h640 : UC6.R6_40_1 (Three.dataOfSetup hS S)) :
    R920L2Even (Three.dataOfSetup hS S) :=
  r920L2Even_of_inputs hK462 hSch _ h63
    (F09.r912L2_of_inputs _ (F09.r99_holds _) (F09.r910_holds _)
      (F09.r911_of h63c _ h640) (F09.r9R5_holds _))
    (F09.r92_of_inputs hK32 hSch _)

theorem r920L2E_dataOfSetup
    (hK462 : UCK.K462) (hK32 : UCK.K32) (hK46 : UCK.K46Semireg)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (h63c : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore)
    (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G) (S : CFSG.LocalAnalysis.RankThreeUC.Setup G)
    (h63 : UC6.R6_3 (Three.dataOfSetup hS S)) (h640 : UC6.R6_40_1 (Three.dataOfSetup hS S))
    (hrest : R920L2Rest (Three.dataOfSetup hS S)) :
    R920L2E (Three.dataOfSetup hS S) :=
  r920L2E_of_parts _
    (r920L2Even_dataOfSetup hK462 hK32 hSch h63c hS S h63 h640)
    (r920L2Three_of_inputs _ (Three.r6_1_dataOfSetup hS S) h63c h640 hK32 hK46 hSch) hrest

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
