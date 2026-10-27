module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1AAAABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1AAAABB
public import CFSG.GH74.KGroups.L27

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_exists_normalizing
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
    (h7 : 7 ∈ D.sig) :
    ∃ E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      E ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ IsElemAbelian 7 E ∧ 7 ^ 3 ≤ Nat.card ↥E ∧
      E ≤ Subgroup.normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) := by
  have hrank := s16h_sl28_seven_pRank_mbar_three D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4 h7
  obtain ⟨E, hEM, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 7)
      (H := Mbar D.M ⊥ V h.hyp151.isElemAbelian) (k := 3) hrank
  refine ⟨E, hEM, hEab, hEcard.ge, ?_⟩
  refine s16h_sl28_seven_le_normalizer_of_odd D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4 h7 E hEM ?_
  rw [hEcard]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
