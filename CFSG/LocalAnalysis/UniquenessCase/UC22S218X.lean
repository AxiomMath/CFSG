module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218NFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3Main
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Main
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5Main
import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2Main
import CFSG.LocalAnalysis.UniquenessCase.UC22S218D4Main
import CFSG.LocalAnalysis.UniquenessCase.UC22S218F4Main
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree c76Three_of_inputs)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_14R (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_8X (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ,
    (IsL3 (BarInf L) n ∨ IsG2 (BarInf L) n ∨ Is3D4 (BarInf L) n ∨
      LieModel (BarInf L) .twistedF4 0 2 n ∨ IsU4 (BarInf L) n ∨ IsU5 (BarInf L) n) →
    ¬ IsPowTwo n → False

@[expose] def S21_8XE (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, ¬ IsPowTwo n → ∀ p ∈ D.sig,
    ((IsL3 (BarInf L) n ∧
        (p = 3 ∧ 3 ∣ 2 ^ n - 1 ∧ (3 ∣ n ∨ 3 ∣ Nat.card (Subgroup.center (Bar2 L))))) ∨
      (IsU4 (BarInf L) n ∧ (p ∣ 2 ^ n + 1 ∧ p ∣ n)) ∨
      (IsU5 (BarInf L) n ∧ (p = 5 ∧ 5 ∣ 2 ^ n + 1))) →
    CFSG.Open.pRank p D.M ≤ 3

@[expose] def S21_8XE2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, ¬ IsPowTwo n → ∀ p ∈ D.sig,
    ((IsL3 (BarInf L) n ∧
        (p = 3 ∧ 3 ∣ 2 ^ n - 1 ∧ (3 ∣ n ∨ 3 ∣ Nat.card (Subgroup.center (Bar2 L))))) ∨
      (IsU5 (BarInf L) n ∧ (p = 5 ∧ 5 ∣ 2 ^ n + 1))) →
    CFSG.Open.pRank p D.M ≤ 3

theorem s21_14_of_s21_14R (D : Data G) (Ch : Choice2011 G) (h8N : S21_8N D Ch)
    (h8X : S21_8X D Ch) (hR : S21_14R D Ch) : S21_14 D Ch := by
  intro hH c L hL hChev
  by_cases hs : ∃ n : ℕ, LieRankTwoEven (BarInf L) n ∧ ¬ IsPowTwo n
  · obtain ⟨n, hn, hnp⟩ := hs
    rcases hn with hX | hX | hX | hX | hX | hX | hX
    · exact (h8X hH c L hL n (Or.inl hX) hnp).elim
    · have hn1 : n ≠ 1 := fun h => hnp ⟨0, by simp [h]⟩
      have h1 : 2 ^ n - 1 ≠ 1 := by
        rcases Nat.lt_or_ge n 2 with h | h
        · interval_cases n
          · simp
          · exact absurd rfl hn1
        · have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
          omega
      obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd h1
      have h := h8N hH c L hL n hX hnp r hr hrn
      exact Or.inr (Or.inl ⟨n, h.2.1.1, h.1.1⟩)
    · exact (h8X hH c L hL n (Or.inr (Or.inl hX)) hnp).elim
    · exact (h8X hH c L hL n (Or.inr (Or.inr (Or.inl hX))) hnp).elim
    · exact (h8X hH c L hL n (Or.inr (Or.inr (Or.inr (Or.inl hX)))) hnp).elim
    · exact (h8X hH c L hL n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX))))) hnp).elim
    · exact (h8X hH c L hL n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hX))))) hnp).elim
  · exact hR hH c L hL hChev fun n hn => by_contra fun hnp => hs ⟨n, hn, hnp⟩

set_option linter.unusedSectionVars false

theorem s21_8X_setup4 (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (Ch : Choice2011 G) (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (hE : S21_8XE (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_8X (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL n hX hn
  have hC76 := c76Three_of_inputs hSE hK3 hB3 hS hU S
  have h76 : ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig,
      IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M →
        Conclusion76 (UC6.dataOfSetup4 hS hU S).M p := fun p hp hsp => by
    by_cases h3 : 3 ∈ uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have h614 := (UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1
  have h4 : 4 ≤ CFSG.Open.pRank S.p (UC6.dataOfSetup4 hS hU S).M :=
    UC6.four_le_pRank_of_sigma S.hp
  rcases hX with hX | hX | hX | hX | hX | hX
  · by_cases hg : S.p = 3 ∧ 3 ∣ 2 ^ n - 1 ∧ (3 ∣ n ∨ 3 ∣ Nat.card (Subgroup.center (Bar2 L)))
    · have := hE hH c L hL n hn S.p S.hp (Or.inl ⟨hX, hg⟩)
      omega
    · have := uc22s218n_pRank_le_three_L3 hGA _ Ch hSg h614 h211 h76 hH c hL hX hn S.hp hg
      omega
  · have := uc22s218n_pRank_le_three_G2 _ Ch hSg h614 h211 h76 hH c hL hX hn S.hp
    omega
  · have := uc22s218n_pRank_le_three_3D4 _ Ch hSg h614 h211 h76 hH c hL hX hn S.hp
    omega
  · have := uc22s218n_pRank_le_three_2F4 _ Ch hSg h614 h211 h76 hH c hL hX hn S.hp
    omega
  · have := uc22s218n_pRank_le_three_U4 hGA _ Ch hSg h614 h211 h76 hH c hL hX hn S.hp
    omega
  · by_cases hg : S.p = 5 ∧ 5 ∣ 2 ^ n + 1
    · have := hE hH c L hL n hn S.p S.hp (Or.inr (Or.inr ⟨hX, hg⟩))
      omega
    · have := uc22s218n_pRank_le_three_U5 hGA _ Ch hSg h614 h211 h76 hH c hL hX hn S.hp hg
      omega

theorem s21_8XE_of_s21_8XE2_setup4 (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (Ch : Choice2011 G) (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (hE : S21_8XE2 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_8XE (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL n hn p hp hcase
  rcases hcase with hcase | ⟨hX, -⟩ | hcase
  · exact hE hH c L hL n hn p hp (Or.inl hcase)
  · have hC76 := c76Three_of_inputs hSE hK3 hB3 hS hU S
    have h76 : ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig,
        IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M →
          Conclusion76 (UC6.dataOfSetup4 hS hU S).M p := fun p hp hsp => by
      by_cases h3 : 3 ∈ uniqueFourBeta G
      · exact hC76 hMS h3 p hp hsp
      · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
    exact uc22s218n_pRank_le_three_U4 hGA _ Ch (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
      ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1) h211 h76 hH c hL hX hn hp
  · exact hE hH c L hL n hn p hp (Or.inr hcase)

theorem s21_14_of_s21_14R_setup4 (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (Ch : Choice2011 G) (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (hE : S21_8XE (UC6.dataOfSetup4 hS hU S) Ch)
    (hR : S21_14R (UC6.dataOfSetup4 hS hU S) Ch) : S21_14 (UC6.dataOfSetup4 hS hU S) Ch :=
  s21_14_of_s21_14R _ Ch (s21_8N_setup4 hSE hK3 hB3 hGA hS hU S hMS hPart Ch h211)
    (s21_8X_setup4 hSE hK3 hB3 hGA hS hU S hMS hPart Ch h211 hE) hR

end CFSG.LocalAnalysis.UniquenessCase.UC22
