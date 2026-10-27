module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_kbar_element
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
    ∃ d : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian),
      d ∈ kBar D.M ⊥ V h.hyp151.isElemAbelian L ∧ orderOf d = 7 ∧
      d ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  obtain ⟨E, hEk, hEab, -, e, heE, heX⟩ :=
    s16h_sl28_seven_kbar_rank_two_noncentral D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
      hthin hZ hbad hrow hZ4 h7
  have he1 : e ≠ 1 := by
    rintro rfl
    exact heX (centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))).one_mem
  have he7 : e ^ 7 = 1 := hEab.2 e heE
  have hdvd : orderOf e ∣ 7 := orderOf_dvd_iff_pow_eq_one.2 he7
  rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) he1
  · exact ⟨e, hEk heE, h, heX⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
