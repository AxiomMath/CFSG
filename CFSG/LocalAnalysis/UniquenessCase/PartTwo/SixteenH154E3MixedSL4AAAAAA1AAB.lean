module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA1AABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_kernel_moves_of_bad
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
    {φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hφM : φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hφ3 : orderOf φ = 3)
    (hcent : ∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian L, φ * a = a * φ)
    (hcentx : ∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x), φ * a = a * φ) :
    ∃ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L, φ z ≠ z := by
  by_contra hcon
  have hfix : ∀ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L, φ z = z := by
    intro z hz
    by_contra hne
    exact hcon ⟨z, hz, hne⟩
  have h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) :=
    s16h_sl4_three_not_dvd_kernel D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
      hbad hrow hZ4 hxM hxn
  obtain ⟨E, hEM, hEX, hEab, hEcard⟩ :=
    s16h_sl4_trivial_scalar_rank_two_X D h hrow h3C hxM hxn hφM hφ3 hcentx hfix
  have hsig : D.sig = {3} :=
    s16h_sl4_bad_three_mem D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 hxM hxn
  have h3sig : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have hlt := hbad 3 h3sig E hEM hEab
  have hinf : E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
      (centSub (wTil ⊥ V h.hyp151.isElemAbelian L)) = E := inf_eq_left.mpr hEX
  rw [hinf] at hlt
  norm_num at hlt
  exact absurd hEcard (not_le.2 hlt)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
