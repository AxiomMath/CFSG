module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Quot
public import CFSG.RankThree.GF2n.Tim79aTINotWC
public import CFSG.RankThree.GF2n.Tim79aSec23Degenerate

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

namespace Hyp

theorem timHyp_quot (h : Hyp X S) (hnd : ∃ d ∈ dSet S, ∃ e ∈ dSet S, orderOf (d * e) = 4) :
    CFSG.Timmesfeld.Hyp (X ⧸ Subgroup.center X)
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) :=
  CFSG.Timmesfeld.image_hyp_center h.exists_isClass h.root h.closure_dSet
    h.le_center_of_isSolvable (fun d hd => h.not_mem_center hd) hnd

theorem false_of_le_rootGroup (h : Hyp X S)
    (hnd : ∃ d ∈ dSet S, ∃ e ∈ dSet S, orderOf (d * e) = 4) {d : X ⧸ Subgroup.center X}
    (hd : d ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S)
    (hle : S.map (QuotientGroup.mk' (Subgroup.center X)) ≤
      CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S) d) : False := by
  have hH := h.timHyp_quot hnd
  haveI := hH.finite
  obtain ⟨d₁, hd₁, e₁, he₁, h41⟩ := hH.nondeg
  obtain ⟨g, hg⟩ := isConj_iff.mp (hH.isConj hd₁ hd)
  have he₂ : g * e₁ * g⁻¹ ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S :=
    hH.conj_mem g he₁
  have h4 : orderOf (d * (g * e₁ * g⁻¹)) = 4 := by
    rw [← hg, show g * d₁ * g⁻¹ * (g * e₁ * g⁻¹) = g * (d₁ * e₁) * g⁻¹ by group,
      CFSG.Timmesfeld.orderOf_conj_eq, h41]
  obtain ⟨y, hy⟩ := isConj_iff.mp (hH.isConj hd he₂)
  have hpair : IsPGroup 2 ↥(CFSG.Timmesfeld.rootGroup
        (QuotientGroup.mk' (Subgroup.center X) '' dSet S) d ⊔
      CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (g * e₁ * g⁻¹)) :=
    CFSG.RankThree.GF2n.Tim79a.isPGroup_rootGroup_sup hH.root hd he₂ h4
  have hF : CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (g * e₁ * g⁻¹) =
      (CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S) d).map
        (MulAut.conj y).toMonoidHom := by
    rw [← hy]
    exact CFSG.Timmesfeld.rootGroup_conj hH.isClass y d
  have hconj : CFSG.Quasithin.conjSubgroup
        (S.map (QuotientGroup.mk' (Subgroup.center X))) y⁻¹ =
      (S.map (QuotientGroup.mk' (Subgroup.center X))).map (MulAut.conj y).toMonoidHom := by
    simp [CFSG.Quasithin.conjSubgroup]
  have hVF : CFSG.Quasithin.conjSubgroup
        (S.map (QuotientGroup.mk' (Subgroup.center X))) y⁻¹ ≤
      CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (g * e₁ * g⁻¹) := by
    rw [hconj, hF]
    exact Subgroup.map_mono hle
  have h2g : IsPGroup 2 ↥(S.map (QuotientGroup.mk' (Subgroup.center X)) ⊔
      CFSG.Quasithin.conjSubgroup (S.map (QuotientGroup.mk' (Subgroup.center X))) y⁻¹) :=
    hpair.to_le (sup_le_sup hle hVF)
  have hcomm := h.pair_map_center (y⁻¹) h2g
  obtain ⟨s, hsS, _, _, hs1, _, _⟩ := h.exists_ne_ne_one
  let a : X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) s
  have haS : a ∈ S.map (QuotientGroup.mk' (Subgroup.center X)) := ⟨s, hsS, rfl⟩
  have ha1 : a ≠ 1 := by
    intro h1
    have hsc : s ∈ Subgroup.center X := (QuotientGroup.eq_one_iff s).1 h1
    have hmem : s ∈ S ⊓ Subgroup.center X := ⟨hsS, hsc⟩
    rw [h.inf_center_eq_bot] at hmem
    exact hs1 (Subgroup.mem_bot.mp hmem)
  have haD : a ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S :=
    h.mem_image_dSet_of_mem_map haS ha1
  have haE : a ∈ CFSG.Timmesfeld.rootSet
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) d :=
    CFSG.Timmesfeld.mem_rootSet_of_mem_rootGroup hH.isClass hd haD (hle haS)
  let b : X ⧸ Subgroup.center X := y * a * y⁻¹
  have hbconj : b ∈ CFSG.Quasithin.conjSubgroup
      (S.map (QuotientGroup.mk' (Subgroup.center X))) y⁻¹ :=
    CFSG.Quasithin.mem_conjSubgroup_iff.mpr (by
      rw [show y⁻¹ * b * (y⁻¹)⁻¹ = a by simp [b, mul_assoc]]
      exact haS)
  have hbD : b ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S := by
    have hbeq : b = y * a * y⁻¹ := rfl
    rw [hbeq]
    exact hH.conj_mem y haD
  have hbG : b ∈ CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) (g * e₁ * g⁻¹) := hVF hbconj
  have hbE : b ∈ CFSG.Timmesfeld.rootSet
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) (g * e₁ * g⁻¹) :=
    CFSG.Timmesfeld.mem_rootSet_of_mem_rootGroup hH.isClass he₂ hbD hbG
  have h4ab : orderOf (a * b) = 4 :=
    CFSG.Timmesfeld.orderOf_mul_eq_four_of_mem_rootSet hH.root hd he₂ haE hbE h4
  have hcommab : a * b = b * a := hcomm a haS b hbconj
  have ha2 : a * a = 1 := by
    simpa [pow_two] using h.isElemAbelian_map_center.2 a haS
  have hb2 : b * b = 1 := by
    show (y * a * y⁻¹) * (y * a * y⁻¹) = 1
    calc (y * a * y⁻¹) * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hsq : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcommab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  have hdvd : orderOf (a * b) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (n := 2) (by rw [pow_two]; exact hsq)
  rw [h4ab] at hdvd
  norm_num at hdvd

theorem isWC_map_center
    (h : Hyp X S) (hnd : ∃ d ∈ dSet S, ∃ e ∈ dSet S, orderOf (d * e) = 4) :
    CFSG.CGT.Timmesfeld75.IsWC (S.map (QuotientGroup.mk' (Subgroup.center X))) := by
  by_contra hwc
  have hH := h.timHyp_quot hnd
  haveI := hH.finite
  have hne : S.map (QuotientGroup.mk' (Subgroup.center X)) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (S.map (QuotientGroup.mk' (Subgroup.center X))) = 1 := by
      rw [hbot, Subgroup.card_bot]
    rw [h.card_map_center] at h1
    have hc : 2 < Nat.card S := h.card
    rw [h1] at hc
    exact absurd hc (by norm_num)
  obtain ⟨d, hd, hle⟩ := CFSG.RankThree.GF2n.Tim79a.tim75aTINotWCRoot_holds
    (X ⧸ Subgroup.center X) (QuotientGroup.mk' (Subgroup.center X) '' dSet S) hH
    (S.map (QuotientGroup.mk' (Subgroup.center X))) hne
    (fun a ha ha1 => h.mem_image_dSet_of_mem_map ha ha1)
    h.isElemAbelian_map_center h.isTI_map_center hwc
  exact h.false_of_le_rootGroup hnd hd hle

theorem psl_or_alt6
    (h : Hyp X S) (hnd : ∃ d ∈ dSet S, ∃ e ∈ dSet S, orderOf (d * e) = 4) :
    (∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL n 2 f) ∨
      Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) := by
  have hH := h.timHyp_quot hnd
  haveI := hH.finite
  have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    (CFSG.Timmesfeld.conclusions _ (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
      hH.isClass hH.root.1 hH.gen hH.oddCore hH.twoCore hH.root.2.1 hH.root.2.2
      hH.nondeg).1.1
  haveI := hsimple
  have hcl := h.classD_map_center
  have hyp : CFSG.CGT.Timmesfeld75.Lemma26Hyp (X ⧸ Subgroup.center X)
      (S.map (QuotientGroup.mk' (Subgroup.center X))) :=
    ⟨h.isWC_map_center hnd, by rw [h.card_map_center]; exact h.card,
      by rw [hcl]; exact hH.isClass, by rw [hcl]; exact hH.root,
      by rw [hcl]; exact hH.gen⟩
  have hnd' : CFSG.CGT.T75E.Lemma26Nondeg
      (S.map (QuotientGroup.mk' (Subgroup.center X))) := by
    rw [CFSG.CGT.T75E.Lemma26Nondeg, hcl]
    exact hH.nondeg
  exact CFSG.RankThree.GF2n.Tim79a.lemma26_psl_or_a6 hyp hnd'

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
