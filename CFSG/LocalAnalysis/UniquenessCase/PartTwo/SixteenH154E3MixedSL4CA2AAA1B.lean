module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1BA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_SL4MixedAux1
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_mixed_fixV_le
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
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
    {r : G} (hrM : r ∈ D.M) (hr3 : orderOf r = 3)
    (hmixed : s16h_SL4Mixed V L h.hyp151.isElemAbelian x r)
    (hrB : barSub ⊥ V h.hyp151.isElemAbelian (Subgroup.zpowers r) ≤
      lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    preTil ⊥ V h.hyp151.isElemAbelian
        (fixV (barSub ⊥ V h.hyp151.isElemAbelian (Subgroup.zpowers r))) ≤
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have hcore := s16h_sl4_mixed_fixVW_le D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
    hbad hrow hZ4 hxM hxn hZ0 hrM hr3 hmixed hrB
  rw [s16h_wSub_inf_centralizer_eq_preTil D h]
  intro g hg
  obtain ⟨x, hx, hxS⟩ := (mem_preTil ⊥ V hV _).1 hg
  exact (mem_preTil ⊥ V hV _).2 ⟨x, hx, hcore hxS⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
