module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1AAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA1BAA
public import CFSG.GroupTheory.PRankCommutingSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_kbar_pRank_two
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
    2 ≤ CFSG.Open.pRank 7 (kBar D.M ⊥ V h.hyp151.isElemAbelian L) := by
  have hdeep : 3 ≤ CFSG.Open.pRank 7
      (lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        kBar D.M ⊥ V h.hyp151.isElemAbelian L) :=
    s16h_sl28_seven_lbar_sup_kbar_pRank_three D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
      hthin hZ hbad hrow hZ4 h7
  set Lb : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) :=
    lBar ⊥ V h.hyp151.isElemAbelian L with hLb
  set Kb : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) :=
    kBar D.M ⊥ V h.hyp151.isElemAbelian L with hKb
  have hKb_eq : Kb = Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
      Subgroup.centralizer (Lb : Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
    rw [hKb, hLb]
    rfl
  have hcomm : Lb ≤ Subgroup.centralizer
      (Kb : Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyc : y ∈ Subgroup.centralizer
        (Lb : Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
      rw [hKb_eq] at hy
      exact (Subgroup.mem_inf.mp hy).2
    exact (Subgroup.mem_centralizer_iff.mp hyc x hx).symm
  have hnot7 : ¬ 7 ∣ Nat.card ↥(Lb ⊓ Kb) := by
    intro hdvd
    obtain ⟨y, hy7⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Lb ⊓ Kb)) 7 hdvd
    have hyL : ((y : ↥(Lb ⊓ Kb)) : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) ∈ Lb :=
      (Subgroup.mem_inf.mp y.2).1
    have hyK : ((y : ↥(Lb ⊓ Kb)) : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) ∈ Kb :=
      (Subgroup.mem_inf.mp y.2).2
    let yL : ↥Lb := ⟨(y : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)), hyL⟩
    have hy7L : orderOf yL = 7 := by
      dsimp only [yL]
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy7]
    have hyL_ne : yL ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hy7L
      omega
    have hyL_center : yL ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      dsimp only [yL]
      change (z : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) *
          (y : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) =
        (y : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) *
          (z : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))
      have hyc : (y : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) ∈ Subgroup.centralizer
          (Lb : Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
        have hyK' : (y : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) ∈
            Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
              Subgroup.centralizer (Lb : Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
          rw [← hKb_eq]
          exact hyK
        exact (Subgroup.mem_inf.mp hyK').2
      exact Subgroup.mem_centralizer_iff.mp hyc _ z.2
    have hcenter_ne : Subgroup.center ↥Lb ≠ ⊥ := by
      intro hbot
      have : yL ∈ (⊥ : Subgroup ↥Lb) := hbot ▸ hyL_center
      exact hyL_ne (Subgroup.mem_bot.mp this)
    have hcard504 : Nat.card ↥Lb = 504 := by
      obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hrow.1
      letI := hKf
      letI := hKfin
      rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKcard]
      norm_num
    haveI : Nontrivial ↥Lb :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard504]; norm_num)
    haveI : Group.IsPerfect ↥Lb := ⟨hcomp.2.2.1⟩
    have hnc : ¬ IsMulCommutative ↥Lb := Group.IsPerfect.not_isMulCommutative ↥Lb
    haveI : IsSimpleGroup ↥Lb := s16h_sl28_eight_simple_of_isSLn_two_three hrow.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Lb) with h | h
    · exact hcenter_ne h
    · exact hnc (Subgroup.center_eq_top_iff.mp h)
  have hadd := CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd
    Nat.prime_seven hcomm hnot7
  have hLb_le : CFSG.Open.pRank 7 Lb ≤ 1 := hthin 7 Nat.prime_seven (by norm_num)
  have hLb_ge : 1 ≤ CFSG.Open.pRank 7 Lb := by
    obtain ⟨y, hy7⟩ := exists_prime_orderOf_dvd_card' (G := ↥Lb) 7
      (s16h_sl28_eight_seven_dvd_card_of_isSLn_two_three hrow.1)
    have hyL : (y : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) ∈ Lb := y.2
    have hy7' : orderOf (y : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) = 7 := by
      rw [Subgroup.orderOf_coe]
      exact hy7
    refine CFSG.SectionRank.le_pRank (by norm_num : 1 < 7)
      (Subgroup.zpowers_le.mpr hyL) ?_ ?_
    · exact CFSG.Open.isElemAbelian_zpowers (by rw [← hy7', pow_orderOf_eq_one])
    · rw [Nat.card_zpowers, hy7', pow_one]
  have hLb_eq : CFSG.Open.pRank 7 Lb = 1 := le_antisymm hLb_le hLb_ge
  rw [hadd, hLb_eq] at hdeep
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
