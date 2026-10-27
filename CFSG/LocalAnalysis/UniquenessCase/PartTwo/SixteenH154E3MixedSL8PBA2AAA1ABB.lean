module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1ABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_kbar_ker_pRank_le_one
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
    CFSG.Open.pRank 7 (kBar D.M ⊥ V h.hyp151.isElemAbelian L ⊓
      centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))) ≤ 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let K : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) :=
    kBar D.M ⊥ V h.hyp151.isElemAbelian L ⊓
      centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
  let Y : Subgroup G := preBarSub D.M ⊥ V h.hyp151.isElemAbelian K
  have hYX : Y ≤ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
      (centSub (wTil ⊥ V h.hyp151.isElemAbelian L)) := by
    dsimp only [Y, K]
    refine s15_Seven_preBarSub_mono h.hyp151.isElemAbelian ?_
    intro x hx
    exact hx.2
  have hYrank_open : CFSG.Open.pRank 7 Y ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (show 1 < 7 by norm_num) hYX).trans
      (s16h_sl28_seven_preBarSub_ker_pRank_le_one D S hσ hJP h hs2 ht ht2 ht1
        htr hW hcomp hthin hZ hbad hrow hZ4 h7)
  have hYrank : CFSG.pRank 7 ↥Y ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hYrank_open
  have hYstab : Y ≤ stabTil ⊥ V := by
    intro g hg
    exact ((mem_preBarSub D.M ⊥ V h.hyp151.isElemAbelian K).1
      (by simpa only [Y] using hg)).2.choose
  let φ₀ : ↥Y →* MulAut (Vtil ⊥ V h.hyp151.isElemAbelian) :=
    (actTil ⊥ V h.hyp151.isElemAbelian).comp (Subgroup.inclusion hYstab)
  have hKbarY : barSub ⊥ V h.hyp151.isElemAbelian Y = K := by
    dsimp only [Y, K]
    rw [barSub_preBarSub]
    exact inf_eq_left.mpr (le_trans inf_le_left (by rw [kBar]; exact inf_le_left))
  let ψ : ↥Y →* ↥K := φ₀.codRestrict K (fun x => by
    rw [← hKbarY]
    refine (mem_barSub ⊥ V h.hyp151.isElemAbelian Y _).2
      ⟨⟨x.1, hYstab x.2⟩, x.2, ?_⟩
    dsimp only [φ₀]
    rw [MonoidHom.comp_apply]
    rfl)
  have hψ : Function.Surjective ψ := by
    intro k
    have hkbar : (k : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) ∈
        barSub ⊥ V h.hyp151.isElemAbelian Y := by
      rw [hKbarY]; exact k.2
    obtain ⟨g, hgY, hgk⟩ :=
      (mem_barSub ⊥ V h.hyp151.isElemAbelian Y _).1 hkbar
    refine ⟨⟨g.1, hgY⟩, ?_⟩
    apply Subtype.ext
    show φ₀ ⟨g.1, hgY⟩ = (k : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))
    rw [← hgk]
    dsimp only [φ₀]
    rw [MonoidHom.comp_apply]
    exact congrArg (actTil ⊥ V h.hyp151.isElemAbelian) (Subtype.ext rfl)
  have hKrank : CFSG.pRank 7 ↥K ≤ 1 :=
    (CFSG.RankThree.OddKernel.pRank_le_of_surjective_of_le_one Nat.prime_seven
      (by norm_num) ψ hψ hYrank).trans hYrank
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact hKrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
