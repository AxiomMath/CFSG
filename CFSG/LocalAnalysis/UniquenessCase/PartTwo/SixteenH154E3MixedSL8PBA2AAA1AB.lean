module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1ABB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_kbar_ker_rank_le_one
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
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    (E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hE : E ≤ kBar D.M ⊥ V h.hyp151.isElemAbelian L ⊓
      centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hEab : IsElemAbelian 7 E) :
    Nat.card ↥E ≤ 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hK := s16h_sl28_seven_kbar_ker_pRank_le_one D S hσ hJP h hs2 ht ht2 ht1 htr
    hW hcomp hthin hZ hbad hrow hZ4 h7
  have hEp : IsPGroup 7 E := hEab.isPGroup
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hnK : n ≤ CFSG.Open.pRank 7 (kBar D.M ⊥ V h.hyp151.isElemAbelian L ⊓
      centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))) :=
    CFSG.SectionRank.le_pRank (show 1 < 7 by norm_num) hE hEab hn
  have hn1 : n ≤ 1 := hnK.trans hK
  rw [hn]
  simpa using Nat.pow_le_pow_right (show 0 < 7 by norm_num) hn1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
