module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeCore
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeAmb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem comm_mem_of_mem {Y : Subgroup G} {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) :
    ⁅x, y⁆ ∈ Y := by
  rw [commutatorElement_def]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem hx hy) (Y.inv_mem hx)) (Y.inv_mem hy)


theorem seven_six_three_member {V H E J A X : Subgroup G} {p : ℕ}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsMulCommutative E) (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hJ : J ≤ pCoreOf 2 H)
    (hJnorm : (J.subgroupOf H).Normal) (hIJ : iSub V H E ≤ J)
    (hA : A ∈ omegaSet V H E) (hJA : J.relIndex A = 2)
    (hJX : J ≤ X) (hXH : X ≤ H) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hXA : X ≤ ⁅X, A⁆ ⊔ J) (hfaith : ∀ a ∈ A, (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J)
    (hexp : ∀ x ∈ X, x ^ p ∈ J) (hcl : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, ⁅⁅x, y⁆, z⁆ ∈ J) :
    J.relIndex X = p ∨ (J.relIndex X = p ^ 3 ∧ ∃ x ∈ X, ∃ y ∈ X, ⁅x, y⁆ ∉ J) := by
  have hAH : A ≤ H := hOmH A hA
  have hJleH : J ≤ H := hJX.trans hXH
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH hJnorm
  have hXnormJ : X ≤ Subgroup.normalizer (J : Set G) := hXH.trans hHnormJ
  haveI : (J.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXnormJ
  have h76 : Hyp76 V H E J A X :=
    hyp76_of_member hV hTI hp hp2 hE hEH hEnorm hOmH hJ hJnorm hIJ hA hJX hXH hAX hfaith hexp
  obtain ⟨Y, hY⟩ := h76.exists_hallCompl
  have hAnJ : ¬ A ≤ J := fun h => by
    have h1 : J.relIndex A = 1 := Subgroup.relIndex_eq_one.mpr h
    omega
  obtain ⟨U, hU, hUAJ, hUY, hAUJ⟩ := h76.exists_normalizing_member hY hA (le_sup_left : A ≤ A ⊔ J)
  have hUnJ : ¬ U ≤ J := fun hUJ => hAnJ (hAUJ.trans (sup_le hUJ le_rfl))
  obtain ⟨u, huU, huJ⟩ := SetLike.not_le_iff_exists.mp hUnJ
  have hUH : U ≤ H := hOmH U hU
  have huH : u ∈ H := hUH huU
  have huJn : u ∈ Subgroup.normalizer (J : Set G) := hHnormJ huH
  have huYn : u ∈ Subgroup.normalizer (Y : Set G) := hUY huU
  have hUab : IsElemAbelian 2 U := isElemAbelian_of_mem_omegaSet hV hU
  have hu2 : u * u = 1 := elemAbelian_mul_self hUab huU
  have hAJrel : J.relIndex (A ⊔ J) = 2 := by
    rw [relIndex_sup_right_of_le_normalizer (hAH.trans hHnormJ)]
    exact hJA
  have hAJle : A ⊔ J ≤ J ⊔ Subgroup.zpowers u :=
    s762C_le_sup_zpowers_of_relIndex_eq_two le_sup_right hAJrel (hUAJ huU) huJ
  have hXu : X ≤ ⁅X, Subgroup.zpowers u⁆ ⊔ J :=
    hXA.trans (commutator_sup_le_of_le_sup hJX (Subgroup.zpowers_le.mpr huJn)
      (le_sup_left.trans hAJle))
  have hYu : Y ≤ ⁅Y, Subgroup.zpowers u⁆ ⊔ iSub V H E :=
    hY.le_commutator_sup hXnormJ huJn huYn hXu
  have hIab : IsElemAbelian 2 (iSub V H E) := seven_two_iSub_isElemAbelian_uncond hV hTI hE hOmH
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun W => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHnormI : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal hEH hEnorm)
  have hYI : Y ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    hY.le_X.trans (hXH.trans hHnormI)
  have huI : u ∈ Subgroup.normalizer (iSub V H E : Set G) := hHnormI huH
  have hexpY : ∀ y ∈ Y, y ^ p ∈ iSub V H E := fun y hy => by
    rw [← hY.inf_J]
    exact ⟨Y.pow_mem hy p, hexp y (hY.le_X hy)⟩
  have hclY : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, ⁅⁅x, y⁆, z⁆ ∈ iSub V H E := fun x hx y hy z hz => by
    rw [← hY.inf_J]
    exact ⟨comm_mem_of_mem (comm_mem_of_mem hx hy) hz,
      hcl x (hY.le_X hx) y (hY.le_X hy) z (hY.le_X hz)⟩
  have hne : iSub V H E ≠ Y :=
    hY.ne_of_faithful hIJ (hAH.trans hHnormJ) hAnJ hfaith
  have hUOm : omegaSet U H E = omegaSet V H E := omegaSet_eq_of_mem hU
  have hUI : iSub U H E = iSub V H E := iSub_eq_of_mem hU
  have hUTI : IsTI U := isTI_of_mem_omegaSet hU hTI
  have hindex : (U ⊓ iSub U H E).relIndex U = 2 := by
    rw [hUI]
    exact (h76.relIndex_eq_two hU hUAJ).2
  have hOmH' : ∀ W ∈ omegaSet U H E, W ≤ H := by
    rw [hUOm]
    exact hOmH
  have hN := nVSub_eq_inf_iSub_of_relIndex_eq_two hUab hUTI hE hEH hEnorm hOmH' hindex
  have hcomm : ⁅iSub V H E, Subgroup.zpowers u⁆ = U ⊓ iSub V H E := by
    rw [← hUI]
    refine commutator_iSub_eq_inf_iSub hUab hUTI hE hEH hEnorm hOmH' (by rw [hUOm]; exact hU)
      hN huU ?_
    rw [hUI]
    exact fun h => huJ (hIJ h)
  have hcommU : ⁅iSub V H E, Subgroup.zpowers u⁆ ≤ U := by
    rw [hcomm]
    exact inf_le_left
  have hcommne : ⁅iSub V H E, Subgroup.zpowers u⁆ ≠ ⊥ := by
    rw [hcomm, inf_iSub_eq_inf_pCoreOf hU]
    exact inf_pCoreOf_ne_bot_of_mem_omegaSet hV hE hEH hEnorm hU
  have hUY' : ∀ w ∈ U, w ∈ Y → w ∈ iSub V H E := fun w hwU hwY =>
    h76.inf_le_iSub_of_isPGroup hY hUab.isPGroup ⟨hwU, hwY⟩
  have hcore := seven_six_three_core hp hp2 hIab hY.iSub_le hYI huI hu2 huYn hexpY hclY hYu hne
    hUTI huU hcommU hcommne hUY'
  rw [hY.relIndex_eq hXnormJ] at hcore
  rcases hcore with h | ⟨h, x, hx, y, hy, hxy⟩
  · exact Or.inl h
  · refine Or.inr ⟨h, x, hY.le_X hx, y, hY.le_X hy, fun hJmem => hxy ?_⟩
    rw [← hY.inf_J]
    exact ⟨comm_mem_of_mem hx hy, hJmem⟩

end CFSG.LocalAnalysis.WeakClosure81
