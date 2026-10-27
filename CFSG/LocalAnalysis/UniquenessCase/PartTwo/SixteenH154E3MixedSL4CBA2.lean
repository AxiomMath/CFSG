module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CBA2C
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BA1A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_engine_b_mbar
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
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    MBarGT D.M ⊥ V D.k := by
  have hk : D.k = 1 :=
    s16h_sl4_bad_k_eq_one D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad hrow
      hZ4 hxM hxn
  have hV := h.hyp151.isElemAbelian
  have hpow : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hcomm : ∀ τ ∈ Mbar D.M ⊥ V hV, τ ^ 2 = 1 → τ ≠ 1 →
      2 ^ (1 + 1) ≤ Nat.card ↥(commSub (⊤ : Subgroup (Vtil ⊥ V hV))
        (Subgroup.zpowers τ)) := by
    intro τ hτ hτ2 hτ1
    have h2 : 2 ≤ rkIdx (fixV (Subgroup.zpowers τ)) :=
      s16h_sl4_engine_b_mbar_involution D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
        hbad hrow hZ4 hτ hτ2 hτ1
    have h3 : 2 ≤ rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers τ)) := by
      rwa [rkIdx_fixV_zpowers, commV_eq_commSub] at h2
    have hcard := card_eq_two_pow hpow
      (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers τ))
    rw [hcard]
    calc 2 ^ (1 + 1) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers τ)) :=
          Nat.pow_le_pow_right (by norm_num) h3
  have hm1 : MBarGT D.M ⊥ V 1 :=
    s16h_e3_mbar_of_rank D h.hyp151.hyp125 (n := 1) hcomm ⟨t, ht, ht2, ht1⟩
  rw [hk]
  exact hm1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
