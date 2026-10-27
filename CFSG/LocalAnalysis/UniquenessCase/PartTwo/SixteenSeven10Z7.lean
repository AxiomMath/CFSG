module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NotConclBig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

private theorem s16c1610_commutator_prod {A B : Type} [Group A] [Group B]
    (hA : _root_.commutator A = ⊤) (hB : _root_.commutator B = ⊤) :
    _root_.commutator (A × B) = ⊤ := by
  rw [_root_.commutator, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod,
    show ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ from hA,
    show ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤ from hB]

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s16c1610_out10_of_case7 (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h : Case168_7 D V₀ V hV L) :
    Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨⟨e⟩, hL3, hsum, -⟩ := h
  obtain ⟨X, -, hXM, hXcard, hXnorm, -⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M V₀ V hV) (p := 7) (center_eq_bot_of_isL3 hL3) e
  have hrk : rk (Vtil V₀ V hV) = 9 := by
    have h9 := s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
    rwa [rk_top] at h9
  exact s16c1610_out10_of_normal_prime D hin.hx hin.h61 hin.h127 hin.h1114 hin.h1214 hin.h162
    hin.h139 h125 (Or.inr rfl) (s16c1610_k_lt_dParam_seven D) hXM hXcard hXnorm
    (by rw [s16c1610_dParam_seven, hrk]; omega)
    (s16c1610_not_concl614_of_rk_odd (by rw [hrk]; decide))

theorem s16c1610_out10_of_case9 (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h : Case168_9 D V₀ V hV L) :
    Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨⟨e⟩, hL3, -, hsum, -⟩ := h
  have hQ : Subgroup.center (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)) = ⊥ := by
    rw [Subgroup.center_prod, center_eq_bot_of_isL3 hL3, Subgroup.bot_prod_bot]
  have hP : _root_.commutator (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)) = ⊤ :=
    s16c1610_commutator_prod (s16c1610_commutator_of_isL3 hL3) (s16c1610_commutator_of_isL3 hL3)
  obtain ⟨X, -, hXM, hXcard, hXnorm, hXc⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M V₀ V hV) (p := 7) hQ e
  obtain ⟨N, hNF, hNcard, hNn⟩ :=
    s16c1610_derived_fstar (Mb := Mbar D.M V₀ V hV) (p := 7) hP e
  have hFM := (s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)).1
  have hW9 : rk ↥(wTil V₀ V hV L) = 9 := s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrk : 9 ≤ rk (Vtil V₀ V hV) := by
    have h9 := rk_mono (le_top : wTil V₀ V hV L ≤ ⊤)
    rwa [rk_top, hW9] at h9
  have hcardN : Nat.card N = 168 * 168 := by
    rw [hNcard, Nat.card_prod, card_eq_of_isL3 hL3]
  have hnot : ¬ Concl614 (Vtil V₀ V hV) (Mbar D.M V₀ V hV) X := by
    refine s16c1610_not_concl614_of_normal_big (m₀ := 5) (by norm_num) (by omega)
      (hNF.trans hFM) ?_ hNn (by rw [hcardN]; norm_num) (by rw [hcardN]; norm_num)
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hXc n (hNF hn) x hx).symm
  exact s16c1610_out10_of_normal_prime D hin.hx hin.h61 hin.h127 hin.h1114 hin.h1214 hin.h162
    hin.h139 h125 (Or.inr rfl) (s16c1610_k_lt_dParam_seven D) hXM hXcard hXnorm
    (by rw [s16c1610_dParam_seven]; omega) hnot

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
