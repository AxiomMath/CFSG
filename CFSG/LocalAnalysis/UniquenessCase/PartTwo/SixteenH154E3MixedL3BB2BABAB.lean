module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BABABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BABABB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_parabolic_factors
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
    (hsig : D.sig = {3}) :
    ∃ P Q : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      P ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧
      Q ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧
      Nat.card ↥P = 24 ∧ Nat.card ↥Q = 24 ∧
      (∀ p ∈ P, p ^ 12 = 1) ∧ (∀ q ∈ Q, q ^ 12 = 1) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧
      P ⊓ Q = ⊥ ∧
      barSub ⊥ V h.hyp151.isElemAbelian D.T ≤
        Subgroup.normalizer ((P ⊔ Q : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
          Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
  obtain ⟨P, hPle, hPcard, hPexp⟩ :=
    s16h_e3_l3_parabolic_first D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hL3 hd2 hsig
  obtain ⟨Q, hQle, hQcard, hQexp, hcomm, hdisj, hnorm⟩ :=
    s16h_e3_l3_parabolic_second_of_first D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ hbad hrow hL3 hd2 hsig hPle hPcard hPexp
  exact ⟨P, Q, hPle, hQle, hPcard, hQcard, hPexp, hQexp, hcomm, hdisj, hnorm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
