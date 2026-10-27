module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

universe u

section Bridge

variable {V : Type u} [CommGroup V]

theorem br_nsmul_eq_zero (hV3 : ∀ v : V, v ^ 3 = 1) (x : Additive V) : (3 : ℕ) • x = 0 := by
  apply Equiv.injective Additive.toMul
  rw [toMul_nsmul, hV3, toMul_zero]

@[expose] def br_addHom (σ : MulAut V) : Additive V →+ Additive V where
  toFun w := Additive.ofMul (σ (Additive.toMul w))
  map_zero' := congrArg (fun x : V => Additive.ofMul x) (map_one σ)
  map_add' a b :=
    congrArg (fun x : V => Additive.ofMul x) (map_mul σ (Additive.toMul a) (Additive.toMul b))

@[expose] def br_lin [Module (ZMod 3) (Additive V)] (σ : MulAut V) : Additive V →ₗ[ZMod 3] Additive V :=
  AddMonoidHom.toZModLinearMap 3 (br_addHom σ)

theorem br_lin_apply [Module (ZMod 3) (Additive V)] (σ : MulAut V) (w : Additive V) :
    br_lin σ w = Additive.ofMul (σ (Additive.toMul w)) := rfl

theorem br_lin_one [Module (ZMod 3) (Additive V)] : br_lin (1 : MulAut V) = 1 := by
  refine LinearMap.ext fun w => ?_
  rw [br_lin_apply, MulAut.one_apply, Module.End.one_apply, ofMul_toMul]

theorem br_lin_mul [Module (ZMod 3) (Additive V)] (σ τ : MulAut V) :
    br_lin (σ * τ) = br_lin σ * br_lin τ := by
  refine LinearMap.ext fun w => ?_
  simp only [Module.End.mul_apply, br_lin_apply, MulAut.mul_apply, toMul_ofMul]

@[expose] def br_rep [Module (ZMod 3) (Additive V)] {B : Type*} [Group B] (ρ : B →* MulAut V) :
    Representation (ZMod 3) B (Additive V) where
  toFun b := br_lin (ρ b)
  map_one' := by
    show br_lin (ρ 1) = 1
    rw [map_one, br_lin_one]
  map_mul' b c := by
    show br_lin (ρ (b * c)) = br_lin (ρ b) * br_lin (ρ c)
    rw [map_mul, br_lin_mul]

theorem br_iff [Module (ZMod 3) (Additive V)] (σ : MulAut V) : σ = 1 ↔ br_lin σ = 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact br_lin_one
  · refine MulEquiv.ext fun v => ?_
    have hv := congrArg (fun T : Additive V →ₗ[ZMod 3] Additive V => T (Additive.ofMul v)) h
    simp only [br_lin_apply, toMul_ofMul, Module.End.one_apply] at hv
    rw [MulAut.one_apply]
    exact Equiv.injective Additive.ofMul hv

theorem br_lin_sub_one_apply [Module (ZMod 3) (Additive V)] (σ : MulAut V) (v : V) :
    (br_lin σ - 1) (Additive.ofMul v) = Additive.ofMul (σ v) - Additive.ofMul v := by
  rw [LinearMap.sub_apply, Module.End.one_apply, br_lin_apply, toMul_ofMul]

theorem br_fixed_card_eq [Module (ZMod 3) (Additive V)] (σ : MulAut V) :
    Nat.card (fixedSubgroup σ) = Nat.card (LinearMap.ker (br_lin σ - 1)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun v => ?_)
  show v ∈ fixedSubgroup σ ↔ Additive.ofMul v ∈ LinearMap.ker (br_lin σ - 1)
  rw [mem_fixedSubgroup, LinearMap.mem_ker, br_lin_sub_one_apply, sub_eq_zero,
    Equiv.apply_eq_iff_eq]

theorem br_card_ker [Module (ZMod 3) (Additive V)] [Finite (Additive V)]
    (T : Additive V →ₗ[ZMod 3] Additive V) :
    Nat.card (LinearMap.ker T) = 3 ^ Module.finrank (ZMod 3) (LinearMap.ker T) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]

theorem br_card [Module (ZMod 3) (Additive V)] [Finite (Additive V)] (σ : MulAut V) :
    Nat.card (fixedSubgroup σ) = 3 ^ Module.finrank (ZMod 3) (LinearMap.ker (br_lin σ - 1)) := by
  rw [br_fixed_card_eq, br_card_ker]

end Bridge

theorem exists_representation {V : Type u} [Group V] [Finite V] (hVc : ∀ v w : V, v * w = w * v)
    (hV3 : ∀ v : V, v ^ 3 = 1) {B : Type*} [Group B] (ρ : B →* MulAut V) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 3) W) (_ : FiniteDimensional (ZMod 3) W)
      (ρ' : Representation (ZMod 3) B W),
      (∀ b : B, ρ b = 1 ↔ ρ' b = 1) ∧
      ∀ b : B, Nat.card (fixedSubgroup (ρ b)) =
        3 ^ Module.finrank (ZMod 3) (LinearMap.ker (ρ' b - 1)) := by
  letI hCG : CommGroup V := { ‹Group V› with mul_comm := hVc }
  have h3 : ∀ x : Additive V, (3 : ℕ) • x = 0 := br_nsmul_eq_zero hV3
  letI hMod : Module (ZMod 3) (Additive V) := AddCommGroup.zmodModule h3
  exact ⟨Additive V, inferInstance, inferInstance, inferInstance, br_rep ρ,
    fun b => br_iff (ρ b), fun b => br_card (ρ b)⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
