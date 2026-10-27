module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_two_rank_normalizer
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    {k : ℕ}
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) k)
    (hk : k ≤ 2)
    (hZbig : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hdim : k = 2 ∧ rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) = 2)
    {τ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hτ : τ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτn : τ ∈ Subgroup.normalizer (lBar ⊥ V h.hyp151.isElemAbelian L :
      Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) :
    4 ≤ rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian)) (Subgroup.zpowers τ)) := by
  haveI : Finite (Vtil ⊥ V h.hyp151.isElemAbelian) := inferInstance
  have hle : commSub (commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
        (lBar ⊥ V h.hyp151.isElemAbelian L)) (Subgroup.zpowers τ) ≤
      commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian)) (Subgroup.zpowers τ) :=
    commSub_mono le_top le_rfl
  exact le_trans (s16h_e3_l3_two_rank_normalizer_W D S h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
    hL3 hk hZbig hdim hτ hτ2 hτ1 hτn) (rk_mono hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
