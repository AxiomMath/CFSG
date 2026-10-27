module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2ABAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_three_ne_bot_three_cent_of_ctilde_coprime
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
    (hsig : D.sig = {3})
    (h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V)) :
    ∃ X : Subgroup G, X ≤ D.M ∧ IsPGroup 3 ↥X ∧ ¬ IsCyclic ↥X ∧
      X ≤ Subgroup.centralizer (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L : Set G) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨E, hE, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (D.M ⊓ Subgroup.centralizer (v1Sub D.M ⊥ V hV L : Set G))
  have hrank := s16h_e3_l3_two_le_pRank_centralizer_of_ctilde_coprime D S hσ hJP h hs2
    ht ht2 ht1 htr hW hcomp hthin hZ hbad hrow hL3 hd2 hsig h3C
  refine ⟨E, hE.trans inf_le_left, hEab.isPGroup, ?_, hE.trans inf_le_right⟩
  refine s16c7_not_isCyclic_of_elemAbelian Nat.prime_three hEab ?_
  rw [hEcard]
  exact Nat.pow_le_pow_right (by norm_num) hrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
