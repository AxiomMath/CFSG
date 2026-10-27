module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2AB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_bb2bababba_good
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
    ∃ v : G, v ∈ V ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  have hV := h.hyp151.isElemAbelian
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨v, hv1mem, hv1, hvT⟩ := s16h_e3_l3_three_ne_bot_v1_fixed D h hZ
  have hvV : v ∈ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV hv1mem
  obtain ⟨X, hXM, hXp, hXnc, hXcent⟩ :=
    s16h_e3_l3_three_ne_bot_three_cent D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ hbad hrow hL3 hd2 hsig
  refine ⟨v, hvV, hvT, centralizer_le_of_noncyclic D S.h61 h3 hXM hXp hXnc hv1 ?_ ?_⟩
  · exact ⟨1, by simpa using hV.2 v hvV⟩
  · intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (Subgroup.mem_centralizer_iff.1 (hXcent hx)) v hv1mem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
