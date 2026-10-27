module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BEB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_zz_cent_eq
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
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
      conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x = ⊥)
    (T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Mbar D.M ⊥ V h.hyp151.isElemAbelian)) :
    T ⊓ centSub (imgTil ⊥ V h.hyp151.isElemAbelian (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L)) =
      T ⊓ (lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) := by
  have hV := h.hyp151.isElemAbelian
  have hTM : T ≤ Mbar D.M ⊥ V hV :=
    ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 hT).1
  have hα := s16h_sl4_zz_cent_eq_alpha D S hσ hJP h hs2 hZ hxM hxn hZ0
  have hβ := s16h_sl4_zz_cent_eq_beta D S hσ hJP h hs2 hW hZ hrow hZ4 hxM hxn
  have hγ := s16h_sl4_zz_cent_eq_gamma D S hσ hJP h hs2 hxM hxn
  refine le_antisymm ?_ ?_
  · intro φ hφ
    rw [Subgroup.mem_inf] at hφ ⊢
    refine ⟨hφ.1, hβ ?_⟩
    rw [Subgroup.mem_inf]
    exact ⟨⟨hTM hφ.1, hα (Subgroup.mem_inf.mpr ⟨hTM hφ.1, hφ.2⟩)⟩, hφ.2⟩
  · intro φ hφ
    rw [Subgroup.mem_inf] at hφ ⊢
    exact ⟨hφ.1, hγ hφ.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
