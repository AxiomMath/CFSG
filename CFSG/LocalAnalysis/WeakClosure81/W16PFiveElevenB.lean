module

import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Open Subgroup
open scoped commutatorElement

theorem commutator_eq_bot_of_odd_of_fixSub_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {A Y : Subgroup (LGL 2 W)} (hA : A ≠ ⊥) (hAe : IsElemAbelian 2 A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set (LGL 2 W))) (hY : Odd (Nat.card Y))
    (hfix : ∀ D : Subgroup (LGL 2 W), D ≤ A → D.relIndex A < 2 ^ 2 → fixSub D = fixSub A) :
    ⁅A, Y⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ D : Subgroup (LGL 2 W), D ≤ A → (D.subgroupOf A).index = 2 →
      ⁅Y ⊓ Subgroup.centralizer (D : Set (LGL 2 W)), A⁆ = ⊥ := by
    intro D hDA hidx
    set C : Subgroup (LGL 2 W) := Y ⊓ Subgroup.centralizer (D : Set (LGL 2 W)) with hC
    set Y₁ : Subgroup (LGL 2 W) := ⁅C, A⁆ with hY₁
    have hY₁leY : Y₁ ≤ Y := by
      rw [hY₁]
      refine Subgroup.commutator_le.mpr fun c hc a ha => ?_
      have hcY : c ∈ Y := hc.1
      have hmem : a * c⁻¹ * a⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hAY ha) c⁻¹).mp (Y.inv_mem hcY)
      rw [commutatorElement_def,
        show c * a * c⁻¹ * a⁻¹ = c * (a * c⁻¹ * a⁻¹) by group]
      exact Y.mul_mem hcY hmem
    have hY₁odd : Odd (Nat.card Y₁) :=
      hY.of_dvd_nat (Subgroup.card_dvd_of_le hY₁leY)
    let P : Subgroup (LGL 2 W) :=
      { carrier := {y | ∀ w ∈ fixSub D, y w = w}
        one_mem' := fun _ _ => rfl
        mul_mem' := fun {x y} hx hy w hw => by
          rw [LinearEquiv.mul_apply, hy w hw, hx w hw]
        inv_mem' := fun {x} hx w hw => by
          simpa [hx w hw] using LinearEquiv.symm_apply_apply x w }
    have hfixDA : fixSub D = fixSub A :=
      hfix D hDA (by show (D.subgroupOf A).index < 2 ^ 2; rw [hidx]; norm_num)
    have hY₁P : Y₁ ≤ P := by
      rw [hY₁]
      refine Subgroup.commutator_le.mpr fun c hc a ha => ?_
      change ∀ w ∈ fixSub D, ⁅c, a⁆ w = w
      intro w hw
      rw [commutatorElement_def]
      show c (a (c⁻¹ (a⁻¹ w))) = w
      have hcw : c w ∈ fixSub D := by
        intro d hd
        have hcomm : d * c = c * d := Subgroup.mem_centralizer_iff.mp hc.2 d hd
        calc d (c w) = (d * c) w := (LinearEquiv.mul_apply d c w).symm
          _ = (c * d) w := by rw [hcomm]
          _ = c (d w) := LinearEquiv.mul_apply c d w
          _ = c w := by rw [hw d hd]
      have hcinv : c⁻¹ w ∈ fixSub D := by
        intro d hd
        have hc2 : c⁻¹ ∈ Subgroup.centralizer (D : Set (LGL 2 W)) :=
          Subgroup.inv_mem _ hc.2
        have hcomm : d * c⁻¹ = c⁻¹ * d := Subgroup.mem_centralizer_iff.mp hc2 d hd
        calc d (c⁻¹ w) = (d * c⁻¹) w := (LinearEquiv.mul_apply d c⁻¹ w).symm
          _ = (c⁻¹ * d) w := by rw [hcomm]
          _ = c⁻¹ (d w) := LinearEquiv.mul_apply c⁻¹ d w
          _ = c⁻¹ w := by rw [hw d hd]
      have haw : a w = w := (hfixDA ▸ hw) a ha
      have ha'w : a⁻¹ w = w := by
        simpa [haw] using LinearEquiv.symm_apply_apply a w
      have hacinv : a (c⁻¹ w) = c⁻¹ w := (hfixDA ▸ hcinv) a ha
      rw [ha'w, hacinv]
      exact LinearEquiv.apply_symm_apply c w
    have hcent : Y₁ ≤ Subgroup.centralizer (D : Set (LGL 2 W)) := by
      rw [hY₁]
      refine Subgroup.commutator_le.mpr fun c hc a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hdc : Commute d c := Subgroup.mem_centralizer_iff.mp hc.2 d hd
      have hda : Commute d a := (hAe.comm ha (hDA hd)).symm
      have h := (((hdc.mul_right hda).mul_right hdc.inv_right).mul_right hda.inv_right).eq
      simpa [commutatorElement_def] using h
    have hcommDA : ∀ x ∈ D, ∀ y ∈ Y₁, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (hcent hy) x hx
    have hfixsub : fixSub D ≤ fixSub Y₁ := fun w hw y hy => (hY₁P hy) w hw
    have hbot : Y₁ = ⊥ :=
      eq_bot_of_pq (p := 2) (V := W) (P := D) (Q := Y₁)
        (hAe.mono hDA).isPGroup (Nat.coprime_two_left.mpr hY₁odd) hcommDA hfixsub
    simpa [hC, hY₁] using hbot
  have hcover :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_hyperplane_generation 2
      Nat.prime_two A Y hAe hA hAY (Nat.coprime_two_left.mpr hY)
  have hle : Y ≤ Subgroup.centralizer (A : Set (LGL 2 W)) := by
    rw [← hcover]
    refine iSup_le fun D => iSup_le fun hDA => iSup_le fun hidx => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (key D hDA hidx)
  have hAcent : A ≤ Subgroup.centralizer (Y : Set (LGL 2 W)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) a ha).symm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAcent

end CFSG.LocalAnalysis.WeakClosure81

end
