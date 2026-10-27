module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NotConclBig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NotConclL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

private theorem s16c1610_commutator_prod_six {A B : Type} [Group A] [Group B]
    (hA : _root_.commutator A = ⊤) (hB : _root_.commutator B = ⊤) :
    _root_.commutator (A × B) = ⊤ := by
  rw [_root_.commutator, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod,
    show ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ from hA,
    show ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤ from hB]

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s16c1610_out10_of_case6 (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h : Case168_6 D V₀ V hV L) :
    Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨⟨e⟩, hshape, -, hσ⟩ := h
  have hQ : Subgroup.center (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)) = ⊥ := by
    rcases hshape with ⟨hA, -⟩ | ⟨hL, -⟩
    · rw [Subgroup.center_prod, s16c1610_center_of_isAlt (by norm_num) hA, Subgroup.bot_prod_bot]
    · rw [Subgroup.center_prod, center_eq_bot_of_isL3 hL, Subgroup.bot_prod_bot]
  have hP : _root_.commutator (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)) = ⊤ := by
    rcases hshape with ⟨hA, -⟩ | ⟨hL, -⟩
    · exact s16c1610_commutator_prod_six (s16c1610_commutator_of_isAlt (by norm_num) hA)
        (s16c1610_commutator_of_isAlt (by norm_num) hA)
    · exact s16c1610_commutator_prod_six (s16c1610_commutator_of_isL3 hL)
        (s16c1610_commutator_of_isL3 hL)
  obtain ⟨X, -, hXM, hXcard, hXnorm, hXc⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M V₀ V hV) (p := 3) hQ e
  obtain ⟨N, hNF, hNcard, hNn⟩ :=
    s16c1610_derived_fstar (Mb := Mbar D.M V₀ V hV) (p := 3) hP e
  have hFM := (s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)).1
  have hNX : N ≤ Subgroup.centralizer (X : Set (MulAut (Vtil V₀ V hV))) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hXc n (hNF hn) x hx).symm
  have hrkW : 6 ≤ rk ↥(wTil V₀ V hV L) := by
    rcases hshape with ⟨-, hsum⟩ | ⟨-, hsum⟩
    · have h8 := s16c1610_rk_sumOfNat_two (r := 4) (fun I hI =>
        s16c1610_rk_of_card_two_pow (s16c1610_card_alternatingNatural_odd (by decide) hI)) hsum
      omega
    · have h6 := s16c1610_rk_sumOfNat_two (r := 3) (fun I hI =>
        s16c1610_rk_binaryNaturalSL hI) hsum
      omega
  have hrk : 6 ≤ rk (Vtil V₀ V hV) := by
    have h1 := rk_mono (le_top : wTil V₀ V hV L ≤ ⊤)
    rw [rk_top] at h1
    omega
  have hnot : ¬ Concl614 (Vtil V₀ V hV) (Mbar D.M V₀ V hV) X := by
    rcases hshape with ⟨hA, hsum⟩ | ⟨hL, hsum⟩
    · have h8 := s16c1610_rk_sumOfNat_two (r := 4) (fun I hI =>
        s16c1610_rk_of_card_two_pow (s16c1610_card_alternatingNatural_odd (by decide) hI)) hsum
      have h1 := rk_mono (le_top : wTil V₀ V hV L ≤ ⊤)
      rw [rk_top] at h1
      have hA60 : Nat.card ↥(lBar V₀ V hV L) = 60 := by
        have := s16c167_two_mul_card_isAlt (by norm_num) hA
        rw [show Nat.factorial 5 = 120 by decide] at this
        omega
      have hcardN : Nat.card N = 3600 := by
        rw [hNcard, Nat.card_prod, hA60]
      exact s16c1610_not_concl614_of_normal_big (m₀ := 4) (by norm_num) (by omega)
        (hNF.trans hFM) hNX hNn (by rw [hcardN]; norm_num) (by rw [hcardN]; norm_num)
    · have hcardN : Nat.card N = 168 * 168 := by
        rw [hNcard, Nat.card_prod, card_eq_of_isL3 hL]
      exact s16c1610_not_concl614_of_normal_l3 hXM hXcard hrk (hNF.trans hFM) hNX hNn hcardN
  exact s16c1610_out10_of_normal_prime D hin.hx hin.h61 hin.h127 hin.h1114 hin.h1214 hin.h162
    hin.h139 h125 (Or.inl rfl)
    (s16c1610_k_lt_dParam_three D hin.hSg hin.h1219 (by rw [hσ]; simp)) hXM hXcard hXnorm
    (by rw [s16c1610_dParam_three]; omega) hnot

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
