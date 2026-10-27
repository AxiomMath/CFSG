module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NotConclBig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10CardOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s16c1610_out10_of_case5 (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h : Case168_5Star D V₀ V hV L) :
    Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨⟨e⟩, hΩ, hnat, hσ⟩ := h
  have hQ : Subgroup.center ↥(lBar V₀ V hV L) = ⊥ := s16c1610_center_of_isOmegaPlus_four_two hΩ
  have hP : _root_.commutator ↥(lBar V₀ V hV L) = ⊤ :=
    s16c1610_commutator_of_isOmegaPlus_four_two hΩ
  obtain ⟨X, -, hXM, hXcard, hXnorm, hXc⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M V₀ V hV) (p := 3) hQ e
  obtain ⟨N, hNF, hNcard, hNn⟩ :=
    s16c1610_derived_fstar (Mb := Mbar D.M V₀ V hV) (p := 3) hP e
  have hFM := (s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)).1
  have hrkV : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) = 8 := by
    have h8 := s16c1610_rk_natOmegaPlus hnat
    omega
  have hrk : 8 ≤ rk (Vtil V₀ V hV) := by
    have h1 := s16c1610_rk_vStar_le (L := L) D h125
    rw [rk_top] at hrkV
    omega
  have hcardN : Nat.card N = 3600 := by
    rw [hNcard, s16c1610_card_of_isOmegaPlus_four_two hΩ]
  have hnot : ¬ Concl614 (Vtil V₀ V hV) (Mbar D.M V₀ V hV) X := by
    refine s16c1610_not_concl614_of_normal_big (m₀ := 4) (by norm_num) (by omega)
      (hNF.trans hFM) ?_ hNn (by rw [hcardN]; norm_num) (by rw [hcardN]; norm_num)
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hXc n (hNF hn) x hx).symm
  exact s16c1610_out10_of_normal_prime D hin.hx hin.h61 hin.h127 hin.h1114 hin.h1214 hin.h162
    hin.h139 h125 (Or.inl rfl)
    (s16c1610_k_lt_dParam_three D hin.hSg hin.h1219 (by rw [hσ]; simp)) hXM hXcard hXnorm
    (by rw [s16c1610_dParam_three]; omega) hnot

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
