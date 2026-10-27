module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_cClos_isPGroup_two
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
    IsPGroup 2 ↥((Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)) := by
  classical
  have hno3 := s16h_sl4_cClos_no_three D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
    hbad hrow hZ4 hxM hxn hZ0 hYM hY3 hYcard hYnc hperm hYL
  let R : Subgroup G := (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)
  have hno3R : ∀ r ∈ R, orderOf r ≠ 3 := fun r hr => hno3 r hr
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hY3
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT2
  have hdisj : Y ⊓ D.T = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y D.T hY3 hT2)
  have hcardH : Nat.card ↥(Y ⊔ D.T) = 3 ^ a * 2 ^ b := by
    rw [CFSG.ABGTheoremB.V56.card_sup_of_permutable hperm hdisj, ha, hb]
  change IsPGroup 2 ↥R
  rw [isPGroup_iff_card_dvd_pow]
  refine ⟨b, ?_⟩
  have hdvdH : Nat.card ↥R ∣ Nat.card ↥(Y ⊔ D.T) :=
    Subgroup.card_dvd_of_le (show R ≤ Y ⊔ D.T from inf_le_left)
  rw [hcardH] at hdvdH
  have hnot3 : ¬ 3 ∣ Nat.card ↥R := by
    intro h3dvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (G := ↥R) h3dvd
    exact hno3R (z : G) z.2 (by rw [Subgroup.orderOf_coe]; exact hz)
  have hcop : Nat.Coprime (Nat.card ↥R) (3 ^ a) :=
    ((Nat.prime_three.coprime_iff_not_dvd).2 hnot3).symm.pow_right a
  exact (hcop.dvd_mul_left).1 hdvdH

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
