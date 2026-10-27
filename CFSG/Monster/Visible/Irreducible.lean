module

public import CFSG.Monster.VisCert.CyclicSpanVis
public import CFSG.Monster.Visible.Faithful

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Lifts CFSG.Monster.VisCert
open scoped IsMulCommutative

instance finite_L2 : Finite L2 := Nat.finite_of_card_ne_zero (by
  rw [← Nat.card_congr phi0Equiv.toEquiv, Nat.card_prod, natCard_C, natCard_cocode]
  norm_num)

@[reducible] def signAct (W : Submodule (ZMod 2) L2)
    (hW : ∀ a : C, ∀ w ∈ W, modTwoEnd (gO a) w ∈ W) : MulAction (Multiplicative C) W where
  smul a w := ⟨modTwoEnd (gO (Multiplicative.toAdd a)) w, hW _ _ w.2⟩
  one_smul w := Subtype.ext (by
    change modTwoEnd (gO (Multiplicative.toAdd 1)) w = w
    rw [toAdd_one, gO_zero, modTwoEnd_one, Module.End.one_apply])
  mul_smul a b w := Subtype.ext (by
    change modTwoEnd (gO (Multiplicative.toAdd (a * b))) w =
      modTwoEnd (gO (Multiplicative.toAdd a)) (modTwoEnd (gO (Multiplicative.toAdd b)) w)
    rw [toAdd_mul, add_comm, gO_add, modTwoEnd_mul, Module.End.mul_apply])

theorem isPGroup_multiplicative_C : IsPGroup 2 (Multiplicative C) :=
  IsPGroup.of_card (n := 12) ((Nat.card_congr Multiplicative.toAdd).trans natCard_C)

theorem zmod_two_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem twoΩCls_mem_of_sign_invariant {W : Submodule (ZMod 2) L2}
    (hW : ∀ a : C, ∀ w ∈ W, modTwoEnd (gO a) w ∈ W) (hne : W ≠ ⊥) : twoΩCls ∈ W := by
  let _ := signAct W hW
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hdvd : 2 ∣ Nat.card W := by
    have h2 : addOrderOf (⟨w, hw⟩ : W) = 2 := by
      refine addOrderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        change (2 : ℕ) • w = 0
        rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_smul]
      · intro h
        exact hw0 (congrArg Subtype.val h)
    exact (congrArg (fun n => n ∣ Nat.card W) h2).mp (addOrderOf_dvd_natCard _)
  have h0 : (0 : W) ∈ MulAction.fixedPoints (Multiplicative C) W := fun a =>
    Subtype.ext (map_zero (modTwoEnd (gO (Multiplicative.toAdd a))))
  obtain ⟨v, hv, hv0⟩ :=
    isPGroup_multiplicative_C.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd h0
  have hvfix : (v : L2) ∈ signFixed :=
    mem_signFixed.2 fun a => congrArg Subtype.val (hv (Multiplicative.ofAdd a))
  rw [signFixed_eq_span, Submodule.mem_span_singleton] at hvfix
  obtain ⟨c, hc⟩ := hvfix
  have hc1 : c = 1 := by
    rcases zmod_two_cases c with h | h
    · exfalso
      apply hv0
      apply Subtype.ext
      rw [← hc, h, zero_smul]
      rfl
    · exact h
  rw [hc1, one_smul] at hc
  rw [hc]
  exact v.2

theorem eq_bot_or_eq_top_of_invariant {W : Submodule (ZMod 2) L2}
    (hW : ∀ p : Pvis, ∀ w ∈ W, modTwoEnd p.1.2 w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hne : W = ⊥
  · exact .inl hne
  right
  have hsign : ∀ a : C, ∀ w ∈ W, modTwoEnd (gO a) w ∈ W := fun a w hw =>
    hW ⟨(YU ⟨a, 0⟩, gO a), YU_gO_mem_Pvis ⟨a, 0⟩⟩ w hw
  have htwo := twoΩCls_mem_of_sign_invariant hsign hne
  rw [eq_top_iff, ← span_orbit_twoΩCls, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  exact hW p _ htwo

@[expose] noncomputable def visModLat : Additive VisMod ≃ₗ[ZMod 2] L2 :=
  visModLinearEquiv.trans phi0Equiv

theorem visModLat_ofMul (y : VisMod) :
    visModLat (Additive.ofMul y) = phi0Equiv (Multiplicative.toAdd (visModEquiv y)) := rfl

theorem phi0Equiv_toAdd_projQ (r : Q) :
    phi0Equiv (Multiplicative.toAdd (projQ r)) = Multiplicative.toAdd (phi (QuotientGroup.mk r)) :=
  (congrArg Multiplicative.toAdd (phi_mk r)).symm

theorem visModLat_mk (r : Q) :
    visModLat (Additive.ofMul (QuotientGroup.mk (rhoN r))) =
      Multiplicative.toAdd (phi (QuotientGroup.mk r)) :=
  (visModLat_ofMul _).trans
    ((congrArg (fun y => phi0Equiv (Multiplicative.toAdd y)) (visModEquiv_mk r)).trans
      (phi0Equiv_toAdd_projQ r))

theorem visModLat_repVis (p : Pvis) (w : Additive VisMod) :
    visModLat (((repVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ :
      LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
        Additive VisMod →ₗ[ZMod 2] Additive VisMod) w) = modTwoEnd p.1.2 (visModLat w) := by
  induction w using Additive.rec with
  | ofMul y =>
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨t, rfl⟩ := rhoN_surjective x
      exact ((congrArg visModLat ((repVis_apply _ (rhoN t)).trans (congrArg Additive.ofMul
        ((conjVis_mk _ _).symm.trans (conjVis_thetaEquiv_mk p t))))).trans (visModLat_mk _)).trans
        ((phi_conjQ p t).trans (congrArg (modTwoEnd p.1.2) (visModLat_mk t).symm))

theorem visible_quotient_irreducible_action :
    (∀ W : Submodule (ZMod 2) (Additive VisMod),
      (∀ g : Gvis ⧸ rhoQvis, ∀ w ∈ W,
        ((repQuot g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
          Additive VisMod →ₗ[ZMod 2] Additive VisMod) w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    (∀ (p : Pvis) (w : Additive VisMod),
      visModLat (((repVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ :
        LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
          Additive VisMod →ₗ[ZMod 2] Additive VisMod) w) = modTwoEnd p.1.2 (visModLat w)) ∧
    (∀ W : Submodule (ZMod 2) L2, (∀ p : Pvis, ∀ w ∈ W, modTwoEnd p.1.2 w ∈ W) →
      W = ⊥ ∨ W = ⊤) := by
  refine ⟨fun W hW => ?_, visModLat_repVis, fun W hW => eq_bot_or_eq_top_of_invariant hW⟩
  let W' : Submodule (ZMod 2) L2 := W.comap (visModLat.symm : L2 →ₗ[ZMod 2] Additive VisMod)
  have hW' : ∀ p : Pvis, ∀ x ∈ W', modTwoEnd p.1.2 x ∈ W' := by
    intro p x hx
    change visModLat.symm (modTwoEnd p.1.2 x) ∈ W
    have e := visModLat_repVis p (visModLat.symm x)
    rw [LinearEquiv.apply_symm_apply] at e
    rw [← e, LinearEquiv.symm_apply_apply]
    exact hW (QuotientGroup.mk ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩) _ hx
  rcases eq_bot_or_eq_top_of_invariant hW' with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have hmem : visModLat w ∈ W' := by
      change visModLat.symm (visModLat w) ∈ W
      rw [LinearEquiv.symm_apply_apply]
      exact hw
    rw [h, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact visModLat.injective (hmem.trans (map_zero visModLat).symm)
  · right
    rw [eq_top_iff]
    intro w _
    have hmem : visModLat w ∈ W' := by
      rw [h]
      exact Submodule.mem_top
    change visModLat.symm (visModLat w) ∈ W at hmem
    rwa [LinearEquiv.symm_apply_apply] at hmem

end CFSG.Monster.Visible
