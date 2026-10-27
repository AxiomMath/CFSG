module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA1
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_zbar_card
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
    Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) = 8 := by
  have hV := h.hyp151.isElemAbelian
  have hpow : Nat.card ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) =
      2 ^ rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) :=
    CFSG.Quasithin.card_eq_two_pow (s15_Infra_vtil_sq_eq_one ⊥ V hV) _
  have h2 : 2 ≤ rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) := by
    have h4 := hZ4
    rw [hpow] at h4
    by_contra hlt
    have hle : rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) ≤ 1 := by omega
    have hpowle : 2 ^ rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) ≤ 2 := by
      simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hle
    omega
  have hle3 : rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) ≤ 3 := by
    have hrow3 := s16fh_row_SL2_three (W := Vtil ⊥ V hV)
      (s15_Infra_vtil_sq_eq_one ⊥ V hV) hrow
    obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hrow.2
    have hdim := s16fh_rk_of_realizes_nat (W := Vtil ⊥ V hV) (K := K) (d := 2) (a := 3)
      hKcard hreal
    omega
  have hne2 := s16h_sl28_seven_zbar_rk_ne_two D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4 h7
  have hrk : rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) = 3 := by omega
  rw [hpow, hrk]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
