module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3WJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Setting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_bad_involution_codim
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {s : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hs : s ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hsq : s ^ 2 = 1) (hs1 : s ≠ 1)
    (hsN : s ∈ Subgroup.normalizer
      ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨L', hne', F, x, hxM, hxn, hconj⟩ := s16h_sl4_exists_x D h hs2
  have hL : barSub ⊥ V hV L ≠ ⊥ := by
    intro h0
    apply hZ
    have h1 : lBar ⊥ V hV L = ⊥ := h0
    have hc : commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (⊥ : Subgroup (MulAut (Vtil ⊥ V hV))) = ⊥ := by
      rw [commSub_eq_bot_iff]
      intro v _ x hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      rfl
    rw [h1, hc]
    exact bot_inf_eq _
  have hJoin : commSub ⊤ (lBar ⊥ V hV L) ⊔ commSub ⊤ L' = ⊤ := by
    have h2 := s16h_wTil_sup_conj_eq_top_of_conc h.hyp151 hV hs2 hL hW hxM hxn
    unfold wTil at h2
    rw [← hconj]
    exact h2
  exact s16h_sl4_frame_involution_rank (s15_Infra_vtil_sq_eq_one ⊥ V hV) F hne'.symm hrow hZ4
    hJoin hs hsq hs1 hsN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
