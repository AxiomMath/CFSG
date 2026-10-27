module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_normalizer_bar
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
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Mbar D.M ⊥ V h.hyp151.isElemAbelian)) :
    ∃ E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      E ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ IsPGroup 7 E ∧ ¬ IsCyclic ↥E ∧
      E ≤ Subgroup.normalizer ((T ⊓ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) : Subgroup _) : Set _) := by
  rcases s16h_sl28_C_TZ_split D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 h7 hxM hxn T hT with hcase | hcase
  · exact s16h_sl28_seven_of_C_TZ_eq_normalizer D S hσ hJP h hs2 ht ht2 ht1 htr hW
      hcomp hthin hZ hbad hrow hZ4 h7 hxM hxn T hT hcase
  · exact s16h_sl28_seven_of_C_TZ_eq_top D S hσ hJP h hs2 ht ht2 ht1 htr hW
      hcomp hthin hZ hbad hrow hZ4 h7 hxM hxn T hT hcase

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
