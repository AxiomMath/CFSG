module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Disp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Rows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_mixed_rank_one
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar V₀ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hZ2 : Nat.card ↥(commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar V₀ V h.hyp151.isElemAbelian L)) ≤ 2)
    (hno : ¬ s16h_H5L3Sum (lBar V₀ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar V₀ V h.hyp151.isElemAbelian L)) 3) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨q, hq⟩ := S.hx.sig_nonempty
  have hpp := D.sig_prime q hq
  obtain ⟨hb, hc⟩ := s16h_H5_rows hJP (s15_Infra_vtil_sq_eq_one V₀ V hV) ht ht2 ht1 htr hW hcomp
    hthin
  have hBB2 : s16h_BlockBound (Mbar D.M V₀ V hV) (barSub V₀ V hV L) q 2 := hb q hpp.1 hpp.2
  have hcfg : s16h_H5Cfg (Mbar D.M V₀ V hV) (lBar V₀ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one V₀ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
  have hdisp := s16h_H5_dispatch_two hJP hcfg hZ hZ2 hno hpp.1 hpp.2
  rcases eq_or_ne V₀ ⊥ with h0 | h0
  · subst h0
    rcases hdisp with hbb1 | hfix
    · exact s16h_unique₁_of_mixed_of_Eb D S hσ h hs2 hq
        (s16h_exists_Eb_of_blockBound_one_two D h hs2.le hq (S.hx.three_le q hq) hbb1) hc
    · exact s16h_uniqueMax_of_fix_two_mixed D S.h61 S.h127 h hs2 hq (S.hx.three_le q hq) hBB2
        hfix hZ2
  · have hv1 := (v1Sub_of_ne_bot D.M V₀ V hV L h0).le
    rcases hdisp with hbb1 | hfix
    · exact s16h_unique₁_of_wSub D h.hyp151 hv1
        (s16h_uniqueMax_of_blockBound_one_two D S.h61 S.h127 h hs2.le hq (S.hx.three_le q hq)
          hbb1)
    · exact s16h_unique₁_of_wSub D h.hyp151 hv1
        (s16h_uniqueMax_of_fix_two D S.h61 S.h127 h hs2.le hq (S.hx.three_le q hq) hBB2 hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
