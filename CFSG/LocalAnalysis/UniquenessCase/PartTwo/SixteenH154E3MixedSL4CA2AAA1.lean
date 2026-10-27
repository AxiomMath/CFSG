module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_SL4MixedAux1
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_mixed_cClos_false
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
    ∀ r ∈ (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G),
      orderOf r = 3 → ¬ s16h_SL4Mixed V L h.hyp151.isElemAbelian x r := by
  intro r hrR hr3 hmixed
  have hV := h.hyp151.isElemAbelian
  obtain ⟨v, hvV, hvcClos, hvZ⟩ :=
    s16h_sl4_cClos_cV_T_not_le_Z D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 hxM hxn hZ0
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hrM : r ∈ D.M := (sup_le hYM D.sylowM.le) hrR.1
  have hstab : Subgroup.zpowers r ≤ stabTil ⊥ V := Subgroup.zpowers_le.2 (hMs hrM)
  have hcomm : r * v = v * r :=
    ((Subgroup.mem_centralizer_iff.1 hrR.2) v hvcClos).symm
  have hrc : r ∈ Subgroup.centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hcomm.symm
  have hfix : v ∈ preTil ⊥ V hV (fixV (barSub ⊥ V hV (Subgroup.zpowers r))) := by
    rw [s15_Glue_mem_preTil_fixV_iff ⊥ V (Subgroup.zpowers r) hV hstab hvV]
    intro e he
    rw [Subgroup.mem_bot]
    have hec : e * v = v * e :=
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.zpowers_le.2 hrc he)) v
        (Set.mem_singleton v)).symm
    rw [hec]
    group
  have hr31 : r ^ 3 = 1 := by
    rw [← hr3]
    exact pow_orderOf_eq_one r
  have hrB := s16h_sl4_barSub_threeElem_le D h hs2 hxM hxn hYM hYL hrR.1 hr31
  have hle := s16h_sl4_mixed_fixV_le D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
    hbad hrow hZ4 hxM hxn hZ0 hrM hr3 hmixed hrB
  exact hvZ (hle hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
