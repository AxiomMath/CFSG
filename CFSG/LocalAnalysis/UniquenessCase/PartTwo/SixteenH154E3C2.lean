module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Mixed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_hyp154_of_component_two_e3
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
 (h880 : F08.R880 D) (hJP : K_JonesParshallH1)
    (h1217 : R1217 D) (hU2 : R8100U2 D) (h920L28 : s16h_e3_R920L28 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2) : Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨hb, hc⟩ := s16h_H5_rows hJP (s15_Infra_vtil_sq_eq_one V₀ V hV)
    ht ht2 ht1 htr hW hcomp hthin
  have hBB2 : ∀ q ∈ D.sig,
      s16h_BlockBound (Mbar D.M V₀ V hV) (barSub V₀ V hV L) q 2 := fun q hq =>
    hb q (D.sig_prime q hq).1 (D.sig_prime q hq).2
  refine s16h_hyp154_of_unique₁_two D h.hyp151 hs2 ?_ (hδ hs2)
  by_cases hA : ∃ q ∈ D.sig, s16h_BlockBound (Mbar D.M V₀ V hV) (barSub V₀ V hV L) q 1
  · obtain ⟨q, hq, hbb1⟩ := hA
    rcases eq_or_ne V₀ ⊥ with h0 | h0
    · subst h0
      exact s16h_unique₁_of_mixed_of_Eb D S hσ h hs2 hq
        (s16h_exists_Eb_of_blockBound_one_two D h hs2.le hq (S.hx.three_le q hq) hbb1) hc
    · exact s16h_unique₁_of_wSub D h.hyp151 (v1Sub_of_ne_bot D.M V₀ V hV L h0).le
        (s16h_uniqueMax_of_blockBound_one_two D S.h61 S.h127 h hs2.le hq
          (S.hx.three_le q hq) hbb1)
  · by_cases hF : commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) = ⊥ ∧
        ∃ q ∈ D.sig, s16h_H5Fix (Mbar D.M V₀ V hV) (barSub V₀ V hV L) q
    · obtain ⟨hZ, q, hq, hfix⟩ := hF
      have hW1 := s16h_uniqueMax_of_fix_two D S.h61 S.h127 h hs2.le hq (S.hx.three_le q hq)
        (hBB2 q hq) hfix
      rcases eq_or_ne V₀ ⊥ with h0 | h0
      · have hv1 : v1Sub D.M V₀ V hV L = ⊥ := s16c167_v1Sub_eq_bot_of_inf_fixV D hV h0 hZ
        intro w hw hw1
        rw [hv1, sup_bot_eq] at hw
        exact hW1 w hw hw1
      · exact s16h_unique₁_of_wSub D h.hyp151 (v1Sub_of_ne_bot D.M V₀ V hV L h0).le hW1
    · by_cases hZ : commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) = ⊥
      · rcases s16h_exc_struct D S hr3 hσ h880 hJP h1217 h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
          (fun q hq hbb => hA ⟨q, hq, hbb⟩)
          (fun q hq hfix => hF ⟨hZ, q, hq, hfix⟩) with hu | hc164
        · exact hu
        · exact absurd hc164 hnot
      · exact s16h_mixed_struct D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
          (fun q hq hbb => hA ⟨q, hq, hbb⟩) hU2 h920L28

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
