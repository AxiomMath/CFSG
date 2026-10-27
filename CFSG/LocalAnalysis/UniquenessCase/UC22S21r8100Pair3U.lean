module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2C
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R77E2Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r8100_pair_three_noOpp {D : Data G}
    (he : evenRank G = 3) (hSg : UC6S846.SigmaStd D)
    (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D) (hU2 : R8100U2 D)
    {L : Subgroup G} {Lp : Fin 2 → Subgroup G} {nvec : Fin 2 → ℕ} {n r p : ℕ}
    {A X : Subgroup G} (hHyp : F08.Hyp8100 D Lp nvec r p A X) (hLp0 : Lp 0 = L)
    (hnvec0 : nvec 0 = n) (hAL : A ≤ L) (hk2 : (conjSetOf D.M L).ncard = 2) (hr5 : 5 < r)
    (hnotStrong : ¬ IsStronglyPEmbedded r D.M)
    {s : ℕ} (hs : Odd s) (hsn : s ∣ n) (hrs : r ∣ 2 ^ s - 1) :
    ((IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) ∧
      A ∈ uniqueSet D.M := by
  obtain ⟨hC, -, hshape, hr, -, hp, hAr, -⟩ := hHyp
  subst hLp0 hnvec0
  have hcong := uc22ine229_cong_of_ncard_two hSg h77 h614 (hC 0) hk2 (hshape 0) hr (by omega)
    (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)) hnotStrong hp
  exact ⟨hcong, hU2 he (Lp 0) (nvec 0) s r p (hC 0) hk2 hcong hs hsn hr hrs hp A hAL hAr⟩

@[expose] def R8100Pair3U (D : Data G) : Prop :=
  evenRank G = 3 → ∀ (L : Subgroup G) (Lp : Fin 2 → Subgroup G) (nvec : Fin 2 → ℕ)
    (n r p s : ℕ) (A X : Subgroup G), F08.Hyp8100 D Lp nvec r p A X → Lp 0 = L → nvec 0 = n →
    A ≤ L → (conjSetOf D.M L).ncard = 2 → 5 < r → ¬ IsStronglyPEmbedded r D.M →
    Odd s → s ∣ n → r ∣ 2 ^ s - 1 →
    ((IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) ∧
      A ∈ uniqueSet D.M

theorem r8100Pair3U_of {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D) (hU2 : R8100U2 D) : R8100Pair3U D :=
  fun he _ _ _ _ _ _ _ _ _ hHyp hLp0 hnvec0 hAL hk2 hr5 hnotStrong hs hsn hrs =>
    r8100_pair_three_noOpp he hSg h77 h614 hU2 hHyp hLp0 hnvec0 hAL hk2 hr5 hnotStrong hs hsn
      hrs

theorem r8100Pair3U_dataOfSetup (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hS : Standing G) (hUC : rankThreeUC G) (S : Setup G)
    (h614 : UC6.R6_14 (dataOfSetup hS S)) (hD : R8100U2D (dataOfSetup hS S)) :
    R8100Pair3U (dataOfSetup hS S) :=
  r8100Pair3U_of (UC6S846.sigmaStd_dataOfSetup hS S)
    (PartTwo.Three.r77E2_dataOfSetup hSE hK3 hS S) h614
    (r8100U2_dataOfSetup_of_r8100U2D hSE hSEZ hG3 hRee hK3 hS hUC S hD)

end CFSG.LocalAnalysis.UniquenessCase.UC22
