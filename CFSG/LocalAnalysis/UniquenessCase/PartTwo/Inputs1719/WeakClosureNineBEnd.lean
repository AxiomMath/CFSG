module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBFive
public import CFSG.LocalAnalysis.WeakClosure81.NineSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNEnd
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGW

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] {N : Subgroup G} {X : Type} [Group X] {π : ↥N →* X}

theorem barSub_commutator {A B : Subgroup G} (hAN : A ≤ N) (hBN : B ≤ N) :
    barSub π ⁅A, B⁆ = ⁅barSub π A, barSub π B⁆ := by
  have hAB : ⁅A, B⁆ ≤ N := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hAN ha) (hBN hb)) (N.inv_mem (hAN ha)))
      (N.inv_mem (hBN hb))
  have h : ⁅A, B⁆.subgroupOf N = ⁅A.subgroupOf N, B.subgroupOf N⁆ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAN,
      Subgroup.map_subgroupOf_eq_of_le hBN, Subgroup.map_subgroupOf_eq_of_le hAB]
  unfold barSub
  rw [h, Subgroup.map_commutator]

theorem faithful_lift (hπ : Function.Surjective π) {U : Subgroup G} (hUN : U ≤ N)
    {Rb Jb : Subgroup X}
    (h : ∀ a ∈ barSub π U, (∀ x ∈ Rb, ⁅a, x⁆ ∈ Jb) → a ∈ Jb) :
    ∀ a ∈ U, (∀ x ∈ liftSub π Rb, ⁅a, x⁆ ∈ liftSub π Jb) → a ∈ liftSub π Jb := by
  intro a ha hax
  have haN := hUN ha
  refine (mem_liftSub_iff ⟨a, haN⟩).2 (h _ (mem_barSub_of_mem haN ha) fun xb hxb => ?_)
  obtain ⟨x, rfl⟩ := hπ xb
  have h1 := hax x ((mem_liftSub_iff x).2 hxb)
  have e : ⁅a, (x : G)⁆ = ((⁅(⟨a, haN⟩ : ↥N), x⁆ : ↥N) : G) := rfl
  rw [e, mem_liftSub_iff, map_commutatorElement] at h1
  exact h1

variable (hker : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
include hker

theorem liftSub_pCoreOf_eq [Finite G] [Finite X] (hπ : Function.Surjective π)
    (K : Subgroup X) : liftSub π (pCoreOf 2 K) = pCoreOf 2 (liftSub π K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (liftSub_pCoreOf_le hker K) ?_
  have hle : pCoreOf 2 (liftSub π K) ≤ N :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (liftSub_le K)
  refine (barSub_le_iff hle).1 (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    (isPGroup_barSub (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)))
  · exact (barSub_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans
      (barSub_liftSub hπ K).le
  · exact (barSub_liftSub hπ K).symm.le.trans
      (barSub_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

end Lift

variable {G : Type} [Group G] [Finite G]

namespace Ctx15

variable {V T N L₁ L₂ : Subgroup G} {X : Type} [Group X] [Finite X] {π : ↥N →* X}
variable (c : Ctx15 V T N L₁ L₂ π)
include c

theorem nine1Hyp_liftSub {Kb Yb : Subgroup X} (hirr : TwoPTwoIrred Kb (Kb ⊓ barSub π T) Yb 3) :
    ∃ Y : Subgroup G, Nine1Hyp V (liftSub π Kb) (liftSub π Kb ⊓ T) Y 3 := by
  have hS : liftSub π (Kb ⊓ barSub π T) = liftSub π Kb ⊓ T := by
    rw [liftSub_inf, c.liftSub_barSub_T]
  obtain ⟨Y, hY, -, -⟩ := twoPTwoIrred_liftSub c.ker c.surj hirr
  rw [hS] at hY
  exact ⟨Y, hY, (liftSub_le Kb).trans c.NM⟩

theorem exists_good_twoResidual {Kb : Subgroup X}
    (hg : ∃ y ∈ Kb, IsGood915 (barSub π L₁) (barSub π L₂) y) :
    ∃ y ∈ twoResidual (liftSub π Kb), y ∈ N ∧ orderOf y = 3 ∧
      (y ∈ L₁ ⊔ pCoreOf 2 N ∨ y ∈ L₂ ⊔ pCoreOf 2 N) := by
  obtain ⟨yb, hyb, hg⟩ := hg
  obtain ⟨y, hyK, hyN, hy3, hgood⟩ :=
    c.exists_good_of_mem_barSub (D := liftSub π Kb) (by rw [barSub_liftSub c.surj]; exact hyb) hg
  exact ⟨y, CFSG.Quasithin.F6.mem_twoResidual_of_odd hyK (by rw [hy3]; decide), hyN, hy3, hgood⟩

theorem not_le_normalizer_wClos {Kb : Subgroup X} {B : Subgroup G} (hB : IsGConj V B)
    (hBS : B ≤ liftSub π Kb ⊓ T)
    (hnorm : ∀ R : Subgroup X, barSub π B ≤ R → R ≤ Kb ⊓ barSub π T →
      ¬ Kb ⊔ (barSub π T ⊓ normalizer ((Kb ⊓ barSub π T : Subgroup X) : Set X)) ≤
        normalizer (R : Set X)) :
    ¬ liftSub π Kb ≤ normalizer (E3.wClos V 0 (liftSub π Kb ⊓ T) : Set G) := by
  intro h1
  have hS : liftSub π (Kb ⊓ barSub π T) = liftSub π Kb ⊓ T := by
    rw [liftSub_inf, c.liftSub_barSub_T]
  obtain ⟨g, rfl⟩ := hB
  apply hnorm (barSub π (E3.wClos V 0 (liftSub π Kb ⊓ T)))
  · exact barSub_mono (conjSubgroup_le_wClos_zero hBS)
  · rw [← barSub_liftSub c.surj (Kb ⊓ barSub π T), hS]
    exact barSub_mono (E3.wClos_le 0 _)
  · refine sup_le ?_ ?_
    · exact (barSub_liftSub c.surj Kb).symm.le.trans (barSub_le_normalizer h1)
    · rintro tb ⟨htb, htbN⟩
      obtain ⟨t, htT, rfl⟩ := htb
      have htS : (t : G) ∈ normalizer ((liftSub π Kb ⊓ T : Subgroup G) : Set G) := by
        rw [← hS]
        exact mem_normalizer_liftSub t.2 htbN
      exact mem_normalizer_barSub (E3.normalizer_le_normalizer_wClos _ htS)

theorem Q_le_pCoreOf (Kb : Subgroup X) : pCoreOf 2 N ≤ pCoreOf 2 (liftSub π Kb) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_liftSub c.ker Kb)
    ((liftSub_le Kb).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)

theorem conj_le_Q_eq {U : Subgroup G} {u : G} (w : Witness V T U u)
    (h2 : ¬ N ≤ normalizer (E3.wClos V 0 T : Set G)) {g₀ : G}
    (hB : conjSubgroup V g₀ ≤ pCoreOf 2 N) : conjSubgroup V g₀ = V := by
  by_contra hBV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, rfl⟩ := w.conj
  obtain ⟨g, hAT, hAQ⟩ := c.exists_conj_not_le h2
  set A := conjSubgroup V g with hAdef
  have hAN : A ≤ N := hAT.trans c.TN
  have hAbel : IsElemAbelian 2 (barSub π A) :=
    ((isElemAbelian_conjSubgroup' c.elem g).subgroupOf N).map π
  rcases c.facts.table _ (barSub_mono hAT) hAbel (c.four_le_card_barSub w hAT hAQ) with
    ⟨Hb, Rb, Lh, hF⟩ | ⟨Kb, Yb, hK⟩
  · exact c.false_of_fiveUse w hAT hF.toFiveUse
  set K := liftSub π Kb with hKdef
  obtain ⟨Y, h91⟩ := c.nine1Hyp_liftSub hK.irr
  have hAK : A ≤ K := (barSub_le_iff hAN).1 hK.le
  have hAS : A ≤ K ⊓ T := le_inf hAK hAT
  obtain ⟨y, hyK, hyN, hy3, hgood⟩ := c.exists_good_twoResidual hK.good
  have hUM : conjSubgroup V h ≤ normalizer (V : Set G) := w.le_T.trans c.T_le_M
  have hBM : conjSubgroup V g₀ ≤ normalizer (V : Set G) :=
    hB.trans (c.Q_le_T.trans c.T_le_M)
  rcases nine_one c.hyp.hyp7 c.hyp.rk_gt h91 with h1 | h2' | h3
  · exact c.not_le_normalizer_wClos ⟨g, hAdef⟩ hAS hK.nonorm h1
  ·
    have hC1K : E3.cClos V 1 T ≤ K := c.cClos_le_liftSub hAT hK.core
    have huS : u ∈ E3.cClos V 1 (K ⊓ T) := by
      refine Subgroup.mem_inf.2 ⟨⟨hC1K ⟨w.le_T w.mem, w.cent_W1⟩, w.le_T w.mem⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.1 w.cent_W1) z (E3.wClos_mono inf_le_right hz)
    have hyc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2' hyK
    have hyu : y * u = u * y := ((Subgroup.mem_centralizer_iff.1 hyc) u huS).symm
    exact c.not_orderOf_three hUM w.ne hyN (centralizer_le_normalizer_conj c.ti h w.mem w.ne_one
      (Subgroup.mem_centralizer_singleton_iff.2 hyu)) hgood hy3
  ·
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (h3.2 (conjSubgroup V g₀) ⟨g₀, rfl⟩ (hB.trans (c.Q_le_pCoreOf Kb)))
    obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (c.conj_ne_bot g₀)
    have hb1' : b ≠ 1 := fun h0 => hb1 (Subtype.ext h0)
    have hyb : y * b = b * y := (Subgroup.mem_centralizer_iff.1 (hc hb)) y hyK
    exact c.not_orderOf_three hBM hBV hyN (centralizer_le_normalizer_conj c.ti g₀ hb hb1'
      (Subgroup.mem_centralizer_singleton_iff.2 hyb)) hgood hy3

theorem false_of_witness (h763 : SevenSixThreeAbelian V) {U : Subgroup G} {u : G}
    (w : Witness V T U u) (h2 : ¬ N ≤ normalizer (E3.wClos V 0 T : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h7 : ∀ g₀ : G, conjSubgroup V g₀ ≤ pCoreOf 2 N → conjSubgroup V g₀ = V :=
    fun g₀ hB => c.conj_le_Q_eq w h2 hB
  obtain ⟨h, rfl⟩ := w.conj
  set U := conjSubgroup V h with hUdef
  set W0 := E3.wClos V 0 T with hW0
  have hUN : U ≤ N := w.le_T.trans c.TN
  have hUQ : ¬ U ≤ pCoreOf 2 N := fun hle => w.ne (h7 h hle)
  have hU4 : 4 ≤ Nat.card (barSub π U) := c.four_le_card_barSub w w.le_T hUQ
  have hUM : U ≤ normalizer (V : Set G) := w.le_T.trans c.T_le_M
  have hUΩ : U ≤ zOmega W0 := fun x hx =>
    ⟨conjSubgroup_le_wClos_zero w.le_T hx, w.cent_W0 hx,
      (isElemAbelian_conjSubgroup' c.elem h).2 x hx⟩
  have hΩT : zOmega W0 ≤ T := fun x hx => E3.wClos_le 0 T hx.1
  have hTW0 : T ≤ normalizer (W0 : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos T)
  have hTΩ : T ≤ normalizer (zOmega W0 : Set G) := NFW.le_normalizer_of_conj_mem fun t ht x hx =>
    ⟨(Subgroup.mem_normalizer_iff.1 (hTW0 ht) x).1 hx.1,
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centralizer (hTW0 ht)) x).1 hx.2.1,
      by rw [conj_pow, hx.2.2, mul_one, mul_inv_cancel]⟩
  rcases c.facts.close (barSub π U) (barSub π (zOmega W0)) (barSub_mono hUΩ) (barSub_mono hΩT)
      (barSub_le_normalizer hTΩ) (((isElemAbelian_zOmega W0).subgroupOf N).map π) hU4 with
    ⟨Hb, Rb, Lh, hF⟩ | ⟨Kb, Yb, hK⟩
  · exact c.false_of_fiveUse w w.le_T hF.toFiveUse
  set K := liftSub π Kb with hKdef
  have hKN : K ≤ N := liftSub_le Kb
  obtain ⟨Y, h91⟩ := c.nine1Hyp_liftSub hK.irr
  have hUK : U ≤ K := (barSub_le_iff hUN).1 hK.le
  have hUS : U ≤ K ⊓ T := le_inf hUK w.le_T
  obtain ⟨y, hyK, hyN, hy3, hgood⟩ := c.exists_good_twoResidual hK.good
  have hfalse : ∀ {z : G}, y * z = z * y → z ∈ U → z ≠ 1 → False := fun hyz hzU hz1 =>
    c.not_orderOf_three hUM w.ne hyN (centralizer_le_normalizer_conj c.ti h hzU hz1
      (Subgroup.mem_centralizer_singleton_iff.2 hyz)) hgood hy3
  rcases nine_one c.hyp.hyp7 c.hyp.rk_gt h91 with h1 | h2' | h3
  · exact c.not_le_normalizer_wClos ⟨h, hUdef⟩ hUS hK.nonorm h1
  ·
    have huS : u ∈ E3.cClos V 1 (K ⊓ T) := by
      refine Subgroup.mem_inf.2 ⟨hUS w.mem, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.1 w.cent_W1) z (E3.wClos_mono inf_le_right hz)
    have hyc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2' hyK
    exact hfalse ((Subgroup.mem_centralizer_iff.1 hyc) u huS).symm w.mem w.ne_one
  by_cases hUO : U ≤ pCoreOf 2 K
  · have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (h3.2 U ⟨h, hUdef⟩ hUO) w.mem
    exact hfalse ((Subgroup.mem_centralizer_iff.1 hc) y hyK) w.mem w.ne_one
  have hUom : U ∈ omegaIn V K (nineE V K) := (h3.1 U ⟨h, hUdef⟩ hUK).resolve_right hUO
  set J := pCoreOf 2 K with hJdef
  have hJeq : liftSub π (pCoreOf 2 Kb) = J := liftSub_pCoreOf_eq c.ker c.surj Kb
  have hJK : J ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hJnorm : (J.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hEK : nineE V K ≤ K := (nineE_le_pCoreOf V K).trans hJK
  have hE := isElemAbelian_nineE V K
  have hEnorm := nineE_subgroupOf_normal V K
  rcases hK.kill with hk1 | ⟨Rb, hJR, hRK, hUR, hodd, hfaith, hne2⟩ |
      ⟨hidx2, Yb', hJY, hYK, hUY, hYcomm, hfaith, hexp, hab, hne3⟩
  ·
    exact hUO (((barSub_le_iff hUN).1 hk1).trans (liftSub_pCoreOf_le c.ker Kb))
  ·
    have hJX : J ≤ liftSub π Rb := hJeq ▸ liftSub_mono hJR
    have hUX : U ≤ normalizer (liftSub π Rb : Set G) := fun a ha =>
      mem_normalizer_liftSub (hUN ha) (hUR (mem_barSub_of_mem (hUN ha) ha))
    have hXodd : Odd (J.relIndex (liftSub π Rb)) := by
      rw [← hJeq, relIndex_liftSub c.surj]
      exact hodd
    have hfaith' : ∀ a ∈ U, (∀ x ∈ liftSub π Rb, ⁅a, x⁆ ∈ J) → a ∈ J := by
      rw [← hJeq]
      exact faithful_lift c.surj hUN hfaith
    have hrel := seven_six_one_relIndex_eq_two_in c.elem c.ti hE.1 hEK hEnorm le_rfl hJnorm
      (fun _ _ => inf_le_right) hJX (liftSub_mono hRK) hUK hUX hXodd hfaith' hUom le_rfl
    apply hne2
    rw [← relIndex_liftSub_left hUN, hJeq]
    exact hrel
  ·
    set Ys := liftSub π Yb' with hYs
    have hYsN : Ys ≤ N := liftSub_le Yb'
    have hJN : J ≤ N := hJK.trans hKN
    have hJb : barSub π J = pCoreOf 2 Kb := by rw [← hJeq, barSub_liftSub c.surj]
    have hJY' : J ≤ Ys := hJeq ▸ liftSub_mono hJY
    have hUY' : U ≤ normalizer (Ys : Set G) := fun a ha =>
      mem_normalizer_liftSub (hUN ha) (hUY (mem_barSub_of_mem (hUN ha) ha))
    have hJU : J.relIndex U = 2 := by
      rw [← hJeq, relIndex_liftSub_left hUN]
      exact hidx2
    have hcN : ⁅Ys, U⁆ ≤ N := Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem (hYsN ha) (hUN hb)) (N.inv_mem (hYsN ha)))
        (N.inv_mem (hUN hb))
    have hYA : Ys ≤ ⁅Ys, U⁆ ⊔ J := by
      have hQ : pCoreOf 2 N ≤ ⁅Ys, U⁆ ⊔ J :=
        ((pCoreOf_le_liftSub c.ker (pCoreOf 2 Kb)).trans hJeq.le).trans le_sup_right
      have hb : barSub π (⁅Ys, U⁆ ⊔ J) = ⁅Yb', barSub π U⁆ ⊔ pCoreOf 2 Kb := by
        rw [barSub_sup hcN hJN, barSub_commutator hYsN hUN, hYs, barSub_liftSub c.surj, hJb]
      calc Ys ≤ liftSub π (⁅Yb', barSub π U⁆ ⊔ pCoreOf 2 Kb) := liftSub_mono hYcomm
        _ = ⁅Ys, U⁆ ⊔ J := by rw [← hb, liftSub_barSub c.ker hQ (sup_le hcN hJN)]
    have hfaith' : ∀ a ∈ U, (∀ y ∈ Ys, ⁅a, y⁆ ∈ J) → a ∈ J := by
      rw [← hJeq]
      exact faithful_lift c.surj hUN hfaith
    have hexp' : ∀ z ∈ Ys, z ^ 3 ∈ J := by
      intro z hz
      obtain ⟨hzN, hzY⟩ := mem_liftSub.1 hz
      rw [← hJeq]
      have e : z ^ 3 = (((⟨z, hzN⟩ : ↥N) ^ 3 : ↥N) : G) := by rw [Subgroup.coe_pow]
      rw [e, mem_liftSub_iff, map_pow]
      exact hexp _ hzY
    have hab' : ∀ z ∈ Ys, ∀ z' ∈ Ys, ⁅z, z'⁆ ∈ J := by
      intro z hz z' hz'
      obtain ⟨hzN, hzY⟩ := mem_liftSub.1 hz
      obtain ⟨hz'N, hz'Y⟩ := mem_liftSub.1 hz'
      rw [← hJeq]
      have e : ⁅z, z'⁆ = ((⁅(⟨z, hzN⟩ : ↥N), ⟨z', hz'N⟩⁆ : ↥N) : G) := rfl
      rw [e, mem_liftSub_iff, map_commutatorElement]
      exact hab _ hzY _ hz'Y
    have hIJ : iSub V K (nineE V K) ≤ J := iSup₂_le fun _ _ => inf_le_right
    have h3' := h763 c.hyp.hyp7 K (nineE V K) J U Ys 3 Nat.prime_three (by norm_num) hEK hEnorm
      hE.1 hIJ le_rfl hJnorm hUom.1 hUK hJU hJY' (liftSub_mono hYK) hUY' hYA hfaith' hexp' hab'
    apply hne3
    rw [← relIndex_liftSub c.surj, hJeq]
    exact h3'

end Ctx15

end CFSG.LocalAnalysis.WeakClosure81.NGW
