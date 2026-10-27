module

public import CFSG.Quasithin.SteinbergCDSolvableFFThreeFitting
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.SteinbergCDOddPlaneTools

public section

namespace CFSG.Quasithin.H13.NQCore


open Subgroup Module
open CFSG.Quasithin.SteinbergCD (glFixedSpace mem_glFixedSpace)
open CFSG.QuasithinUnique.Setup.Offender (weight fixSub mem_fixSub)

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
@[expose] noncomputable def contragredient :
    LinearMap.GeneralLinearGroup (ZMod 2) W →*
      (Module.Dual (ZMod 2) W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W) where
  toFun g := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W g⁻¹).dualMap
  map_one' := by
    ext f w
    rfl
  map_mul' g h := by
    ext f w
    rfl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem contragredient_apply (g : LinearMap.GeneralLinearGroup (ZMod 2) W)
    (f : Module.Dual (ZMod 2) W) (w : W) :
    contragredient g f w =
      f (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w) :=
  rfl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem contragredient_injective [Finite W] :
    Function.Injective (contragredient (W := W)) := by
  have : Module.Free (ZMod 2) W := Module.Free.of_divisionRing (ZMod 2) W
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ∀ w : W, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w = w := by
    intro w
    rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff (ZMod 2)]
    intro f
    have h2 : contragredient g f w = f w := by rw [hg]; rfl
    rw [contragredient_apply] at h2
    rw [map_sub, h2, sub_self]
  have h3 : g⁻¹ = 1 := Units.ext (LinearMap.ext h1)
  rw [← inv_inv g, h3, inv_one]

variable [Finite W] {Γ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}

theorem card_mul_card_glFixedSpace_lt (hsolv : Group.IsSolvable ↥Γ) (hO2 : CFSG.pCore 2 ↥Γ = ⊥)
    (h3 : ¬ 3 ∣ Nat.card Γ) {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hAΓ : A ≤ Γ) (hA : IsElementaryAbelian 2 ↥A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card (glFixedSpace A) < Nat.card W := by
  set e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W with he
  set Γ' := Γ.map e.toMonoidHom with hΓ'
  set eΓ : ↥Γ ≃* ↥Γ' := Γ.equivMapOfInjective _ e.injective with heΓ
  have : Group.IsSolvable ↥Γ' := Group.isSolvable_of_surjective (f := eΓ.toMonoidHom) eΓ.surjective
  have hO2' : CFSG.pCore 2 ↥Γ' = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 eΓ, hO2, Subgroup.map_bot]
  have h3' : ¬ 3 ∣ Nat.card Γ' := by rwa [← Nat.card_congr eΓ.toEquiv]
  set A' := A.map e.toMonoidHom with hA'
  have eA : ↥A ≃* ↥A' := A.equivMapOfInjective _ e.injective
  have hfix : fixSub (MonoidHom.id _) A' = glFixedSpace A := by
    ext w
    rw [mem_fixSub, mem_glFixedSpace]
    constructor
    · intro h a ha
      exact h _ ⟨a, ha, rfl⟩
    · rintro h _ ⟨a, ha, rfl⟩
      exact h a ha
  obtain ⟨-, -, h⟩ := SteinbergCD.solvable_two_core_free_FF_action_three_in_fitting
    (k := ZMod 2) (H := Γ') hO2'
  have hlt := h h3' A' (map_mono hAΓ) (isElementaryAbelian_of_mulEquiv' eA hA)
    (fun hb => hA1 ((map_eq_bot_iff_of_injective A e.injective).mp hb))
  rw [weight, hfix, ← Nat.card_congr eA.toEquiv] at hlt
  exact hlt

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem card_mul_card_invariant_dual_lt (hsolv : Group.IsSolvable ↥Γ)
    (hO2 : CFSG.pCore 2 ↥Γ = ⊥) (h3 : ¬ 3 ∣ Nat.card Γ)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)} (hAΓ : A ≤ Γ)
    (hA : IsElementaryAbelian 2 ↥A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {f : Module.Dual (ZMod 2) W //
      ∀ a ∈ A, ∀ w, f ((a : W →ₗ[ZMod 2] W) w) = f w} <
        Nat.card (Module.Dual (ZMod 2) W) := by
  have : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) W => (f : W → ZMod 2))
      DFunLike.coe_injective
  set κ := contragredient (W := W) with hκ
  have hκi : Function.Injective κ := contragredient_injective
  set Γ' := Γ.map κ with hΓ'
  set eΓ : ↥Γ ≃* ↥Γ' := Γ.equivMapOfInjective _ hκi with heΓ
  have : Group.IsSolvable ↥Γ' := Group.isSolvable_of_surjective (f := eΓ.toMonoidHom) eΓ.surjective
  have hO2' : CFSG.pCore 2 ↥Γ' = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 eΓ, hO2, Subgroup.map_bot]
  have h3' : ¬ 3 ∣ Nat.card Γ' := by rwa [← Nat.card_congr eΓ.toEquiv]
  set A' := A.map κ with hA'
  have eA : ↥A ≃* ↥A' := A.equivMapOfInjective _ hκi
  have hfix : ∀ f : Module.Dual (ZMod 2) W, f ∈ fixSub (MonoidHom.id _) A' ↔
      ∀ a ∈ A, ∀ w, f ((a : W →ₗ[ZMod 2] W) w) = f w := by
    intro f
    rw [mem_fixSub]
    constructor
    · intro h a ha w
      have h1 := congrArg (fun φ : Module.Dual (ZMod 2) W => φ w) (h _ ⟨a⁻¹, inv_mem ha, rfl⟩)
      rw [MonoidHom.id_apply, contragredient_apply, inv_inv] at h1
      exact h1
    · rintro h _ ⟨a, ha, rfl⟩
      ext w
      rw [MonoidHom.id_apply, contragredient_apply]
      exact h _ (inv_mem ha) w
  obtain ⟨-, -, h⟩ := SteinbergCD.solvable_two_core_free_FF_action_three_in_fitting
    (k := ZMod 2) (H := Γ') hO2'
  have hlt := h h3' A' (map_mono hAΓ) (isElementaryAbelian_of_mulEquiv' eA hA)
    (fun hb => hA1 ((map_eq_bot_iff_of_injective A hκi).mp hb))
  rw [weight, ← Nat.card_congr eA.toEquiv] at hlt
  have hc : Nat.card (fixSub (MonoidHom.id _) A') = Nat.card {f : Module.Dual (ZMod 2) W //
      ∀ a ∈ A, ∀ w, f ((a : W →ₗ[ZMod 2] W) w) = f w} :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  rw [hc] at hlt
  exact hlt

end CFSG.Quasithin.H13.NQCore
