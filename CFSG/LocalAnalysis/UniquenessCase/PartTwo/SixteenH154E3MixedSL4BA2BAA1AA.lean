module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BA2BAA1AAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_engine_a_involution_normalizer_reduce
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
    {s : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hs : s ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hsq : s ^ 2 = 1) (hs1 : s ≠ 1)
    (hsN : s ∈ Subgroup.normalizer
      ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Nat.card K = 4)
      (s' : MulAut (StdMod (Fin 2) K)),
      s' ∈ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧ s' ^ 2 = 1 ∧ s' ≠ 1 ∧
      rkIdx (fixV (Subgroup.zpowers s')) ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  have hfix := s16h_sl4_row_involution_codim D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4 hs hsq hs1 hsN
  obtain ⟨-, K, hKf, hKfin, hKcard, -⟩ := hrow
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨s', hs'N, hs'2, hs'1, hs'le⟩ := s16h_sl4_natNorm_transvection (K := K) hKcard
  refine ⟨K, hKf, hKfin, ?_, s', hs'N, hs'2, hs'1, ?_⟩
  · rw [hKcard]
    norm_num
  · exact le_trans hs'le hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
