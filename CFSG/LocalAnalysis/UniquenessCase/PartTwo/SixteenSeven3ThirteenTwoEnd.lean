module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3OddNc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3ThirteenOneB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapAEmpty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapBeta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapM

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_false_of_case4_gt3 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h111 : W3Thm111 G) (hM : S16GapMGtOne D) (hAE : S16GapAEmpty D)
    (hβ : S16GapBetaBound D) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV)
    (h1 : Case168_9 D ⊥ V hV L → v1Sub D.M ⊥ V hV L = ⊥)
    (hr : ∃ r : ℕ, 3 < r ∧ Case168_4With D ⊥ V hV L r)
    (hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ ≠ ⊥) : False := by
  have hh : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hP := hh.pairFacts
  obtain ⟨A, hA, hA1⟩ : ∃ A ∈ E3.gammaSet V D.k D.T,
      ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV A⁆ ≠ ⊥ := by
    by_contra hne
    push Not at hne
    exact hcomm (s16c167_comm_wClos_of_forall hh hne)
  obtain ⟨hAT, g, hAg, hmQ⟩ := E3.mem_gammaSet_iff.1 hA
  have hm : 1 < mBar D.M ⊥ V hV := hM V L hV hc
  have hChoice : Choice1613 D ⊥ V hV L A := by
    unfold Choice1613
    exact ⟨hA, Or.inl hA1⟩
  have hVgM : ¬ conjSubgroup V g ≤ D.M :=
    s16c167_not_le_M_of_choice D hx h61 hV hc hm rfl h1 hChoice hAg
  have hVg' : ¬ V ≤ conjSubgroup D.M g := by
    intro hVM
    obtain ⟨r, hr3, hr'⟩ := hr
    have hcase : Case168_3 D ⊥ V hV L ∨ (∃ r : ℕ, 3 ≤ r ∧ Case168_4With D ⊥ V hV L r) ∨
        Case168_8 D ⊥ V hV ∨ Case168_9 D ⊥ V hV L ∨ Case168_10 D ⊥ V hV L ∨
        Case168_11 D ⊥ V hV L :=
      Or.inr (Or.inl ⟨r, hr3.le, hr'⟩)
    have hempty := hAE V L hV hc hcase
    have hne := s16c167_calABar_nonempty_of_le_conj D hx h61 h111 hc.setting.hyp16 hm hVM hVgM
    exact (Set.not_nonempty_iff_eq_empty.2 hempty) hne
  have hbeta := hβ V L hV hc hr
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAel : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV g)
  have hAst : A ≤ stabTil ⊥ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hbotbar : barSub ⊥ V hV A ≠ ⊥ := by
    intro h0
    exact hA1 (by rw [h0, Subgroup.commutator_bot_right])
  have hAB : A ≤ conjSubgroup V g ⊓ D.M := le_inf hAg hAM
  have hall : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B < 2 →
      V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G) := by
    intro B hBA hlt
    have hBM : B ≤ conjSubgroup V g ⊓ D.M := hBA.trans hAB
    have hmB : E3.mQuot (conjSubgroup V g) B ≤ D.k + 1 := by
      rw [E3.mQuot_add hBA hAg, hmQ]
      omega
    have hmBar : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) ≤ D.k :=
      hmQ ▸ E3.mQuot_mono hAB
    have hr' : ((E3.mQuot (conjSubgroup V g) B + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) <
        rMV D.M V := by
      rw [show mSub (⊥ : Subgroup G) = 0 from rk_bot, add_zero]
      exact lt_of_le_of_lt (by exact_mod_cast hmB) hbeta.2
    have hβ' : (E3.mQuot (conjSubgroup V g) B : ℕ∞) <
        betaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V :=
      lt_of_le_of_lt (by exact_mod_cast hmB) (lt_of_lt_of_le hbeta.1 (betaN_anti hmBar))
    have hcomm0 := six_two_three hh.hyp62 hBM hr' hVg' hβ'
    refine le_antisymm ?_ (inf_le_inf_left _ (Subgroup.centralizer_le hBA))
    intro c hc'
    refine ⟨hc'.1, ?_⟩
    show c ∈ centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hmem : ⁅c, a⁆ ∈ (⊥ : Subgroup G) :=
      hcomm0 ▸ Subgroup.commutator_mem_commutator hc' (hAB ha)
    exact (commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 hmem)).symm
  have hmem : barSub ⊥ V hV A ∈ calABar 2 D.M ⊥ V hV :=
    s16c167_barSub_mem_calABar_of_le hV rfl hAM hAst hAel hbotbar hall
  have hXodd : Odd (Nat.card (oddBar D.M ⊥ V hV)) :=
    Nat.coprime_two_left.mp (coprime_card_relPPrimeCore Nat.prime_two (Mbar D.M ⊥ V hV))
  have hMbarNorm : Mbar D.M ⊥ V hV ≤
      normalizer (oddBar D.M ⊥ V hV : Set (MulAut (Vtil ⊥ V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (relPPrimeCore_le (Mbar D.M ⊥ V hV))).1
      (relPPrimeCore_normal Nat.prime_two (Mbar D.M ⊥ V hV))
  exact hA1 (thin_four_twentySix_commutator_eq_bot (s15_Infra_vtil_sq_eq_one ⊥ V hV) hmem hXodd
    ((barSub_mono ⊥ V hV hAM).trans hMbarNorm))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
