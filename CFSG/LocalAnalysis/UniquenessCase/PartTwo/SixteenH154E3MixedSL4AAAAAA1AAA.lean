module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA1AAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_kernel_three_of_bad
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
    ∃ φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian),
      φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ orderOf φ = 3 ∧
      (∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian L, φ * a = a * φ) ∧
      (∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x), φ * a = a * φ) := by
  have hV := h.hyp151.isElemAbelian
  have h3 : 3 ∣ Nat.card ↥(Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) ⊓
      Subgroup.centralizer (lBar ⊥ V hV (conjSubgroup L x) :
        Set (MulAut (Vtil ⊥ V hV)))) :=
    s16h_sl4_kernel_three_dvd_of_bad D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
      hbad hrow hZ4 hxM hxn
  obtain ⟨φ, hφ3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨(φ : MulAut (Vtil ⊥ V hV)), φ.2.1.1, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hφ3
  · intro a ha
    exact (Subgroup.mem_centralizer_iff.mp φ.2.1.2 a ha).symm
  · intro a ha
    exact (Subgroup.mem_centralizer_iff.mp φ.2.2 a ha).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
