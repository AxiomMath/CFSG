module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34AlphaDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2NoSwap
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Out
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2RowsF1
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Swap
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Deg5
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2F1
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunCommute
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.Adapters.TauCetiExceptional.ReeCatalog
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL3EpsOdd17)

theorem uc22s2112r34_funTwoType_five_dvd {t : StatedLieTag} {n p f : ℕ} (ht : FunTwoType t n)
    (h5 : 5 ∣ (genericOrders t n p f).1) : (t = .PSL ∨ t = .PSU) ∧ n = 5 := by
  cases t
  case PSL =>
    rcases ht with rfl | rfl
    · have h : 5 ∣ Nat.gcd 4 (p ^ f - 1) := h5
      exact absurd (h.trans (Nat.gcd_dvd_left 4 _)) (by norm_num)
    · exact ⟨Or.inl rfl, rfl⟩
  case PSU =>
    rcases ht with rfl | rfl
    · have h : 5 ∣ Nat.gcd 4 (p ^ f + 1) := h5
      exact absurd (h.trans (Nat.gcd_dvd_left 4 _)) (by norm_num)
    · exact ⟨Or.inr rfl, rfl⟩
  case PSp =>
    have h : 5 ∣ Nat.gcd 2 (p ^ f - 1) := h5
    exact absurd (h.trans (Nat.gcd_dvd_left 2 _)) (by norm_num)
  case POmegaOdd =>
    have h : 5 ∣ 2 := h5
    exact absurd h (by norm_num)
  case POmegaMinus =>
    have h : 5 ∣ Nat.gcd 4 ((p ^ f) ^ n + 1) := h5
    exact absurd (h.trans (Nat.gcd_dvd_left 4 _)) (by norm_num)
  case G2 =>
    have h : 5 ∣ 1 := h5
    exact absurd h (by norm_num)
  case trialityD4 =>
    have h : 5 ∣ 1 := h5
    exact absurd h (by norm_num)
  all_goals exact False.elim ht

section ExcTwoFun


@[expose] def UC22ExcTwoFun (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (p : ℕ), p.Prime → 7 ≤ p →
    LieModel X t 0 p 1 →
    (∀ (S : Sylow 2 X) (K₁ K₂ : Subgroup X),
      K₁ ∈ F14.FunSet (fundPred p) X (S : Subgroup X) →
      K₂ ∈ F14.FunSet (fundPred p) X (S : Subgroup X) → K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ →
      (∃ w ∈ (S : Subgroup X), K₁.map (MulAut.conj w).toMonoidHom = K₂) ∨
        UC22NoSwapInput p (S : Subgroup X) K₁ K₂) ∧
    ∀ K K' : Subgroup X, IsFundamentalOver p K → IsFundamentalOver p K' →
      ∀ x ∈ K ⊓ K', (orderOf x).Prime → 5 ≤ orderOf x → orderOf x ≠ p → K = K'

@[expose] def UC22ExcTwoFunWeak (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (p : ℕ), p.Prime → 7 ≤ p →
    LieModel X t 0 p 1 →
    (∀ (S : Sylow 2 X) (K₁ K₂ : Subgroup X),
      K₁ ∈ F14.FunSet (fundPred p) X (S : Subgroup X) →
      K₂ ∈ F14.FunSet (fundPred p) X (S : Subgroup X) → K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ →
      (∃ w ∈ (S : Subgroup X), K₁.map (MulAut.conj w).toMonoidHom = K₂) ∨
        UC22NoSwapInput p (S : Subgroup X) K₁ K₂) ∧
    ∀ K K' : Subgroup X, IsFundamentalOver p K → IsFundamentalOver p K' →
      ∀ x ∈ K ⊓ K', (orderOf x).Prime → 5 ≤ orderOf x → orderOf x ≠ p →
        K = K' ∨ 2 ≤ Open.pRank p (centralizer ({x} : Set X))

theorem UC22ExcTwoFun.weak {t : StatedLieTag} (h : UC22ExcTwoFun t) : UC22ExcTwoFunWeak t :=
  fun X _ _ _ p hp hp7 hX => ⟨(h X p hp hp7 hX).1, fun K K' hK hK' x hx h₁ h₂ h₃ =>
    Or.inl ((h X p hp hp7 hX).2 K K' hK hK' x hx h₁ h₂ h₃)⟩

end ExcTwoFun

variable {G : Type} [Group G] [Finite G]


theorem uc22s2112r34_false_swap_rows_exc (hKS : KFunSplit) (hGA : GriessAllModelsStatement)
    {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t 0 p 1) (ht : t = .G2 ∨ t = .trialityD4) (hp7 : 7 ≤ p)
    (hX : LieModel (BarInf L) t 0 p 1) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hinn : ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hexc : UC22ExcTwoFunWeak t) : False := by
  have hKC : KFunCount := kFunCount_holds
  have hFC : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommute :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunCommute_of_funHypOmega
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunHypOmega_holds
  have ht2 : FunTwoType t 0 := by
    rcases ht with rfl | rfl <;> trivial
  have hd : ∀ s : ℕ, s.Prime → s ≠ 2 → ¬ s ∣ (genericOrders t 0 p 1).1 := by
    intro s hs _ hdvd
    have h1 : (genericOrders t 0 p 1).1 = 1 := by
      rcases ht with rfl | rfl <;> rfl
    rw [h1] at hdvd
    exact hs.one_lt.ne' (Nat.dvd_one.1 hdvd)
  have hπN : ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 →
      ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
    uc22s2112r34_not_dvd_radical_of_gO hGA CFSG.TauCetiBridge.typewiseBridges c hL hp
      (by omega : 5 ≤ p) hX hd
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  obtain ⟨hswap, huniq⟩ := hexc (BarInf L) p hp hp7 hX
  have hL3 : ¬ IsL3EpsOdd17 (BarInf L) p := by
    obtain ⟨hA1, hA3, hRee⟩ := uc22s2112r34_funTwoType_ne ht2
    obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1
      (fun h => hA3 ⟨h.1, h.2.1⟩) hRee hpN
    rcases h4 with ⟨hexc', -⟩ | h4
    · exact uc22s2112r34_not_isL3EpsOdd17_of_exc hp hX hexc'
    · exact uc22s2112r34_not_isL3EpsOdd17 hp (by rwa [← pRank_eq_pRank_barInf hp hpN])
  refine uc22s2112r34_false_swap_or_noswap hKS hKC hFC hσ hKF7 hH c hn3 hL hBN hfaith hp hp2
    hadm ht2 (by simpa using hp7) hX hno hree hpσ hpN hinn hπN ?_ ?_
  · intro P K₁ K₂ h₁ h₂ hne
    have hcomm := uc22s2112r34_funSet_commute_barInf hFC hL hp hp2 hX hno hL3 hree
      (by rw [pow_one]; omega) P h₁ h₂ hne
    rw [pow_one] at h₁ h₂
    exact hswap P K₁ K₂ h₁ h₂ hne hcomm
  · rw [pow_one]
    exact huniq

theorem uc22s2112r34_false_even2_f1 (hKS : KFunSplit) (hGA : GriessAllModelsStatement)
    {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p 1) (ht : FunTwoType t n) (hp7 : 7 ≤ p)
    (hX : LieModel (BarInf L) t n p 1) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hG2 : UC22ExcTwoFun .G2) (hD4 : UC22ExcTwoFunWeak .trialityD4) (hRk : TriD4OuterThreeRank)
    (hSec : TriD4OuterThreeSection) : False := by
  cases t
  case PSL =>
    rcases ht with rfl | rfl
    · exact uc22s2112r34_false_swap_rows_f1 hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2 hadm
        (Or.inl ⟨rfl, Or.inl rfl⟩) hp7 hX hno hree hpσ hpN
    · by_cases h5 : 5 ∣ p - 1
      · exact uc22s2112r34_false_swap_rows_deg5_f1 hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp
          hp2 hadm (Or.inl rfl) (Nat.dvd_gcd (dvd_refl 5) (by simpa using h5)) hp7 hX hno hree
          hpσ hpN
      · exact uc22s2112r34_false_swap_rows_f1 hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2
          hadm (Or.inl ⟨rfl, Or.inr ⟨rfl, h5⟩⟩) hp7 hX hno hree hpσ hpN
  case PSU =>
    rcases ht with rfl | rfl
    · exact uc22s2112r34_false_swap_rows_f1 hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2 hadm
        (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)) hp7 hX hno hree hpσ hpN
    · by_cases h5 : 5 ∣ p + 1
      · exact uc22s2112r34_false_swap_rows_deg5_f1 hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp
          hp2 hadm (Or.inr rfl) (Nat.dvd_gcd (dvd_refl 5) (by simpa using h5)) hp7 hX hno hree
          hpσ hpN
      · exact uc22s2112r34_false_swap_rows_f1 hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2
          hadm (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, h5⟩⟩)) hp7 hX hno hree hpσ hpN
  case PSp =>
    obtain rfl : n = 2 := ht
    exact uc22s2112r34_false_swap_rows_f1 hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2 hadm
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) hp7 hX hno hree hpσ hpN
  case POmegaOdd =>
    obtain rfl : n = 3 := ht
    exact uc22s2112r34_false_swap_rows_orth hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2 hadm
      (Or.inl ⟨rfl, rfl⟩) hp7 hX hno hree hpσ hpN
  case POmegaMinus =>
    obtain rfl : n = 4 := ht
    exact uc22s2112r34_false_swap_rows_orth hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2 hadm
      (Or.inr ⟨rfl, rfl⟩) hp7 hX hno hree hpσ hpN
  case G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    have hinn : ∀ b (hb : b ∈ c.B0),
        inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈
          (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
      intro b hb
      have hdvd : orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) ∣ orderOf b := by
        have h := orderOf_map_dvd (inducedBarInfAutHom L)
          (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G)))
        simpa [Subgroup.orderOf_mk] using h
      exact uc22s2112r34_inner_of_squarefree_f1_exc hadm hX (Or.inr (Or.inr (Or.inl rfl)))
        (Odd.of_dvd_nat (ch214_odd_card c.hpi)
          (hdvd.trans (Subgroup.orderOf_dvd_natCard c.B0 hb)))
        (Squarefree.squarefree_of_dvd hdvd (Ctx23L.orderOf_squarefree_of_mem_calB1 c.hB0 hb))
        (fun h => by cases h)
    exact uc22s2112r34_false_swap_rows_exc hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2 hadm
      (Or.inl rfl) hp7 hX hno hree hpσ hpN hinn hG2.weak
  case trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    by_cases hinn : ∀ b (hb : b ∈ c.B0),
        inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range
    · exact uc22s2112r34_false_swap_rows_exc hKS hGA hσ hKF7 hH c hn3 hL hBN hfaith hp hp2 hadm
        (Or.inr rfl) hp7 hX hno hree hpσ hpN hinn hD4
    ·
      push Not at hinn
      obtain ⟨b, hb, hout⟩ := hinn
      have h1 : (genericOrders .trialityD4 0 p 1).1 = 1 := rfl
      have hπN : ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 →
          ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
        uc22s2112r34_not_dvd_radical_of_gO hGA CFSG.TauCetiBridge.typewiseBridges c hL hp
          (by omega : 5 ≤ p) hX fun s hs _ hdvd => hs.one_lt.ne' (Nat.dvd_one.1 (h1 ▸ hdvd))
      exact uc22s2112r34_false_d4_outer hRk hSec hσ hKF7 hH c hL hBN hfaith hp hp7 hadm hX hpσ
        hpN hπN hb hout
  all_goals exact False.elim ht


theorem s21_12aFR34F2Even2_of_exc (hKS : KFunSplit) (hGA : GriessAllModelsStatement)
    {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h5 : S21_5 D Ch) (h82 : F08.R82 D)
    (h211 : S21_1 D Ch) (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hG2 : UC22ExcTwoFun .G2) (hD4 : UC22ExcTwoFunWeak .trialityD4) (hRk : TriD4OuterThreeRank)
    (hSec : TriD4OuterThreeSection) : S21_12aFR34F2Even2 D (Choice214U D) := by
  intro hH c _heven _hpow L hL p hp hp2 hpσ t n f hadm ht hq7 hcase hX hno hfaith
  exfalso
  have hn3' : 3 ≤ c.n := hn3 hH (c.mono hCh)
  have hBN : c.B0 ≤ normalizer (L : Set G) :=
    h5 hH { c.mono hCh with B := c.B0, hB := c.hB0, hle := le_rfl } L hL
  have hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f := fun f hm =>
    uc22s2112r34_ree_false hGA h82 h211 hH (c.mono hCh) hL hm
  obtain ⟨hA1, -, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
    (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨by omega, hA1⟩))
  by_cases hf1 : f = 1
  · subst hf1
    exact uc22s2112r34_false_even2_f1 hKS hGA hσ hKF7 hH c hn3' hL hBN hfaith hp hp2 hadm ht
      (by simpa using hq7) hX hno hree hpσ hpN hG2 hD4 hRk hSec
  · obtain ⟨hn4, h5d⟩ := hcase.resolve_left hf1
    have hf2 : 2 ≤ f := by
      have := hadm.2.1
      omega
    obtain ⟨ht5, rfl⟩ := uc22s2112r34_funTwoType_five_dvd ht h5d
    exact uc22s2112r34_false_deg5_f2 hKS kFunCount_holds
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunCommute_of_funHypOmega
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunHypOmega_holds)
      hGA CFSG.TauCetiBridge.typewiseBridges hσ hKF7 hH c hn4 hL hBN hfaith hp hp2 ht5 hadm hf2
      h5d hX hno hree hpσ hpN

end CFSG.LocalAnalysis.UniquenessCase.UC22
