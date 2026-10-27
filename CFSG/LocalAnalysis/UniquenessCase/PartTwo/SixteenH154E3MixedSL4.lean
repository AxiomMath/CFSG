module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_mixed_sl2_four_unique
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
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨x, hxM, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 (by omega)
  rcases s16h_sl4_z0_dichotomy D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad hrow
      hZ4 hxM hxn with hbot | heq
  · intro w hw hw1
    exact (s16h_sl4_engine_a_false D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 hxM hxn hbot).elim
  · intro w hw hw1
    exact (s16h_sl4_engine_b_false D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 hxM hxn heq).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
