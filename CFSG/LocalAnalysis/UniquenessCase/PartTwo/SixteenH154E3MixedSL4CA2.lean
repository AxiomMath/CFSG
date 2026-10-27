module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

private theorem s16h_two_pGroup_orderOf_ne_three {H : Subgroup G} (hH : IsPGroup 2 ↥H)
    {r : G} (hr : r ∈ H) : orderOf r ≠ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨r, hr⟩
  have hk' : orderOf r = 2 ^ k := by simpa using hk
  intro h3
  have h23 : (2 : ℕ) ^ k = 3 := by rw [← hk', h3]
  by_cases hk0 : k = 0
  · subst hk0
    norm_num at h23
  · have hdvd : 2 ^ 1 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    rw [h23] at hdvd
    norm_num at hdvd

theorem s16h_sl4_engine_b_cClos_no_three
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
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
    {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y) (hYcard : Nat.card ↥Y = 9)
    (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T)
    (hYL : barSub ⊥ V h.hyp151.isElemAbelian Y ≤ lBar ⊥ V h.hyp151.isElemAbelian L ⊔
      lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    ∀ r ∈ (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G), orderOf r ≠ 3 := by
  intro r hrR
  exact s16h_two_pGroup_orderOf_ne_three
    (s16h_sl4_cClos_isPGroup_two D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 hxM hxn hZ0 hYM hY3 hYcard hYnc hperm hYL) hrR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
