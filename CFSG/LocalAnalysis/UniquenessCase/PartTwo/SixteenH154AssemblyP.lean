module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyPA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Blocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UElem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_hyp154_of_pgroup (D : Data G) (S : s16h_Std D)
    (h4 : 3 < CFSG.Open.evenRank G) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (h133 : Conc4_133 (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hnp : ¬ (Nat.card ↥(lBar V₀ V h.hyp151.isElemAbelian L)).Prime) : Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  have hc : Conc4_136 D V₀ V hV L := ⟨t, ht, ht2, ht1, htr, hW⟩
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.hyp151.le
  have hσ3 : ∃ q ∈ D.sig, 3 ≤ CFSG.Open.pRank q D.M := by
    obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    exact ⟨q, hq, S.hx.three_le q hq⟩
  obtain ⟨p, hp, hLc, hLt, hind, hrows⟩ := h133
  rcases hrows with ⟨hcyc, -⟩ | ⟨hcyc, -⟩ | ⟨hP, hrk6⟩ | ⟨hE, hrk8, hx6, -⟩ |
    ⟨hcyc, -⟩ | h6 | ⟨hE, hrk6, hinv⟩
  · exact absurd (hcyc.2.symm ▸ (by norm_num : Nat.Prime 3)) hnp
  · exact absurd (hcyc.2.symm ▸ (by norm_num : Nat.Prime 5)) hnp
  ·
    by_cases h3 : 3 ∈ D.sig
    · have h2 : 2 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L) := by
        rw [← CFSG.Quasithin.pRank_top_subtype (lBar V₀ V hV L)]
        exact s16h_two_le_pRank_of_isPOnePlusTwo hP
      exact s16c34_hyp154_of_pRank D S.h61 S.h127 h h3 (S.hx.three_le 3 h3) h2 hs hδ
    · obtain ⟨B, hBL, hB1, hBe, hBc, hBd⟩ :=
        s16h_der_exists_central_of_extraspecial (A := Mbar D.M V₀ V hV)
          (L := lBar V₀ V hV L) (p := 3) (by norm_num) hLM hP
      have hU₂ := s16h_condU2_of_central_derived D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111
        S.h112 S.hThin S.hCyc S.h127 hσ h hc (by norm_num) (by norm_num) hBL hB1 hBe hBc hBd
      have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by rw [hP.2.1]; norm_num
      exact s16h_hyp154_of_central D S h4 hσ h hδ hs hU₂ h3 (Or.inl ⟨hP, hrk6⟩) hodd
  ·
    by_cases h3 : 3 ∈ D.sig
    · have h2 : 2 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L) := s16h_bl_le_pRank (by norm_num) hE
      exact s16c34_hyp154_of_pRank D S.h61 S.h127 h h3 (S.hx.three_le 3 h3) h2 hs hδ
    · have htn : t ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) := by
        rcases s16h_bl_mem_normalizer_or_rk hW hind ht htr with hh | hh
        · exact hh
        · omega
      obtain ⟨B, hBL, hB1, hBe, hBc, hBd⟩ :=
        s16h_der_exists_central_of_abelian (A := Mbar D.M V₀ V hV)
          (L := lBar V₀ V hV L) ht hLM htn hE hLt
      have hU₂ := s16h_condU2_of_central_derived D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111
        S.h112 S.hThin S.hCyc S.h127 hσ h hc (by norm_num) (by norm_num) hBL hB1 hBe hBc hBd
      have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
        rw [s16h_dc_card_of_elem hE]; norm_num
      exact s16h_hyp154_of_central D S h4 hσ h hδ hs hU₂ h3
        (Or.inr (Or.inr ⟨hE, hrk8, hx6⟩)) hodd
  · exact absurd (hcyc.2.symm ▸ (by norm_num : Nat.Prime 7)) hnp
  ·
    obtain ⟨r, m, hpm, hr2, hE, hrkm, hD⟩ := h6
    by_cases h32 : p = 3 ∧ r = 2
    ·
      have hp3 : p = 3 := h32.1
      have hr2' : r = 2 := h32.2
      have hm2 : m = 2 := by
        rcases hpm with ⟨-, hm⟩ | ⟨hp7, -⟩
        · exact hm
        · exact absurd (hp3.symm.trans hp7) (by norm_num)
      have hE32 : IsElemAbelianOfRank 3 2 ↥(lBar V₀ V hV L) := by
        rw [hp3, hr2'] at hE
        exact hE
      have hrk6 : rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 6 := by
        rw [hrkm, hr2', hm2]
      by_cases h3 : 3 ∈ D.sig
      · have h2 : 2 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L) :=
          s16h_bl_le_pRank (by norm_num) hE32
        exact s16c34_hyp154_of_pRank D S.h61 S.h127 h h3 (S.hx.three_le 3 h3) h2 hs hδ
      · have htn : t ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) := by
          rcases s16h_bl_mem_normalizer_or_rk hW hind ht htr with hh | hh
          · exact hh
          · omega
        obtain ⟨B, hBL, hB1, hBe, hBc, hBd⟩ :=
          s16h_der_exists_central_of_abelian (A := Mbar D.M V₀ V hV)
            (L := lBar V₀ V hV L) ht hLM htn hE32 hLt
        have hU₂ := s16h_condU2_of_central_derived D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111
          S.h112 S.hThin S.hCyc S.h127 hσ h hc (by norm_num) (by norm_num) hBL hB1 hBe hBc hBd
        have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
          rw [s16h_dc_card_of_elem hE32]; norm_num
        exact s16h_hyp154_of_central D S h4 hσ h hδ hs hU₂ h3
          (Or.inr (Or.inl ⟨hE32, hrk6⟩)) hodd
    ·
      have hp2 : p ≠ 2 := by
        rcases hpm with ⟨hp3, -⟩ | ⟨hp7, -⟩ <;> omega
      have hd := s16h_bl_le_commutator_of_deltaSym (s15_Infra_vtil_sq_eq_one V₀ V hV)
        hW ht2 htr hp hp2 hpm hr2 h32 hLM hE hLt hD
      have hLe := s16h_bl_isElemAbelian hE
      have hr := hr2.trans (s16h_bl_le_pRank hp.one_lt hE)
      have hU := s16h_condU_of_derived_elemAbelian D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111
        S.h112 S.hThin S.hCyc S.h127 hσ h hc hp hp2 hLe hr hd
      exact s16h_hyp154_of_condU D S.h61 h hσ3 hU hs hδ
  ·
    have hL3 : ∀ x ∈ lBar V₀ V hV L, x ^ 3 = 1 := (s16h_bl_isElemAbelian hE).2
    have hd := s16h_bl_le_commutator_of_inverted ht hLM hL3 hinv
    have hLe := s16h_bl_isElemAbelian hE
    have hr := s16h_bl_le_pRank (by norm_num : (1 : ℕ) < 3) hE
    have hU := s16h_condU_of_derived_elemAbelian D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111
      S.h112 S.hThin S.hCyc S.h127 hσ h hc (by norm_num) (by norm_num) hLe hr hd
    exact s16h_hyp154_of_condU D S.h61 h hσ3 hU hs hδ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
