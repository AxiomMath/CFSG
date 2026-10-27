module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_mixed_l3_unique
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
    (hrow : s16h_H5RowL3 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hbig : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∨
      s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3) :
    ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  intro w hw hw1
  have hsums := (s16h_H5RowL3_iff (lBar ⊥ V h.hyp151.isElemAbelian L)
    (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
    (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L))).1 hrow
  rcases hbig with hZbig | hthree
  · obtain ⟨k, hk3, hsumk⟩ := hsums
    rcases Nat.lt_or_ge k 3 with hk | hk
    · exact False.elim (s16h_e3_l3_mixed_two_big_false D S hσ hJP h hs2 ht ht2 ht1 htr
        hW hcomp hthin hZ hbad hrow hsumk (by omega) hZbig)
    · have hk' : k = 3 := by omega
      have hsum3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
          (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
          (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3 := by
        simpa [hk'] using hsumk
      exact False.elim (s16h_e3_l3_mixed_three_ne_bot_false D S hσ hJP h hs2 ht ht2 ht1
        htr hW hcomp hthin hZ hbad hrow hsum3)
  · exact False.elim (s16h_e3_l3_mixed_three_ne_bot_false D S hσ hJP h hs2 ht ht2 ht1 htr
      hW hcomp hthin hZ hbad hrow hthree)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
