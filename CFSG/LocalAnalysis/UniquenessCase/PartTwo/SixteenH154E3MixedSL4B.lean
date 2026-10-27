module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIRoute
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TID
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BA2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_engine_a_false
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
      conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x = ⊥) : False := by
  obtain ⟨P, hPN, hP3, hPnc⟩ :=
    s16h_sl4_zz_normalizer D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad hrow hZ4
      hxM hxn hZ0
  have h3 : 3 ∈ D.sig :=
    s16h_sl4_engine_a_three_mem D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 hxM hxn
  exact s16h_e3_ti_V1_false D S.h61 S.h127 h.hyp151.hyp125.2 (s16h_e3_v1_inCalV D h hZ)
    (s16h_e3_v1_hw D h hs2 hxM hxn h3 Nat.prime_three (s16h_sl4_sup_pRank_two D h hrow hxM hxn))
    h3 hPN hP3 hPnc (s16h_e3_v1_card_ge_eight D h hs2 hxM hxn hZ4 hZ0)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
