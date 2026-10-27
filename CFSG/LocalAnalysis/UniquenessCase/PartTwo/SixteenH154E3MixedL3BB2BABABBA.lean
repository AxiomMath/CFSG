module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Engine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BABABBAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BABABBAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BABABBAC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_three_ne_bot_dim_le_two_false_aux
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
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2)
    (hsig : D.sig = {3}) : False := by
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨Y, hYM, hY3, -, hYexp, hYnc, hYperm⟩ :=
    s16h_e3_l3_bb2bababba_permuting D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ hbad hrow hL3 hd2 hsig
  obtain ⟨v, hvV, hvT, hvC⟩ :=
    s16h_e3_l3_bb2bababba_good D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ hbad hrow hL3 hd2 hsig
  exact s16h_e3_false_of_permuting_three D S hσ h h3
    (s16h_e3_l3_bb2bababba_mbarGT D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ hL3 hd2)
    hYM hY3 hYexp hYnc hYperm (Or.inr (Or.inr ⟨v, hvV, hvT, hvC⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
