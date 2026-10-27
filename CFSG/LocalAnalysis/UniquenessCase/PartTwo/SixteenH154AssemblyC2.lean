module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Rows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_hyp154_of_component_two
    (D : Data G) (S : s16h_Std D)
    (h4 : 3 < CFSG.Open.evenRank G) (hσ : D.sig = D.sig1) (hJP : K_JonesParshallH1)
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
  obtain ⟨q, hq⟩ := S.hx.sig_nonempty
  obtain ⟨hb, hc⟩ := s16h_H5_rows hJP (s15_Infra_vtil_sq_eq_one V₀ V hV)
    ht ht2 ht1 htr hW hcomp hthin
  have hb' : s16h_BlockBound (Mbar D.M V₀ V hV) (barSub V₀ V hV L) q 2 :=
    hb q (D.sig_prime q hq).1 (D.sig_prime q hq).2
  have hu1 : ∀ w ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
    by_cases h0 : V₀ = ⊥
    · subst V₀
      exact s16h_unique₁_of_mixed D S h4 hσ h hs2 hq hb' hc
    · have hv1 : v1Sub D.M V₀ V hV L ≤ V₀ := (v1Sub_of_ne_bot D.M V₀ V hV L h0).le
      exact s16h_unique₁_of_wSub D h.hyp151 hv1
        (s16h_uniqueMax_of_blockBound_two D S.h61 S.h127 h hs2.le hq
          (S.hx.four_le h4 q hq) hb')
  exact s16h_hyp154_of_unique₁_two D h.hyp151 hs2 hu1 (hδ hs2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
