module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.StandardType

section Ree

open TensorProduct

open scoped TensorProduct

private theorem commute_of_sq_eq_one {Q : Type} [Group Q] (hQ : ∀ x : Q, x ^ 2 = 1) (x y : Q) :
    x * y = y * x := by
  have hs : ∀ z : Q, z * z = 1 := fun z => by simpa [pow_two] using hQ z
  have h1 : x * y * x * y = 1 := by
    have := hs (x * y)
    simpa only [mul_assoc] using this
  have h2 : x * y * x = y := by
    calc x * y * x = x * y * x * (y * y) := by rw [hs y, mul_one]
      _ = (x * y * x * y) * y := (mul_assoc (x * y * x) y y).symm
      _ = 1 * y := by rw [h1]
      _ = y := one_mul y
  calc x * y = x * y * (x * x) := by rw [hs x, mul_one]
    _ = (x * y * x) * x := (mul_assoc (x * y) x x).symm
    _ = y * x := by rw [h2]

private theorem exists_fixed_vector_of_simple {Γ : Type} [Group Γ] [Finite Γ] (e : Γ)
    (hW : ∀ (W : Type) [AddCommGroup W] [Module (AlgebraicClosure (ZMod 2)) W]
      [Module.Finite (AlgebraicClosure (ZMod 2)) W]
      (ρ : Representation (AlgebraicClosure (ZMod 2)) Γ W)
      [IsSimpleModule (MonoidAlgebra (AlgebraicClosure (ZMod 2)) Γ) ρ.asModule],
      ∃ w : W, w ≠ 0 ∧ ρ e w = w) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (AlgebraicClosure (ZMod 2)) V]
      [Module.Finite (AlgebraicClosure (ZMod 2)) V] [Nontrivial V]
      (ρ : Representation (AlgebraicClosure (ZMod 2)) Γ V),
      Module.finrank (AlgebraicClosure (ZMod 2)) V = n → ∃ v : V, v ≠ 0 ∧ ρ e v = v := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih V _ _ _ _ ρ hfin
  classical
  by_cases hirr : ρ.IsIrreducible
  · haveI : IsSimpleModule (MonoidAlgebra (AlgebraicClosure (ZMod 2)) Γ) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
    exact hW V ρ
  · have hbot_top : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
      intro h
      have hsub : (⊥ : Submodule (AlgebraicClosure (ZMod 2)) V) = ⊤ :=
        congrArg Subrepresentation.toSubmodule h
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hvmem : v ∈ (⊥ : Submodule (AlgebraicClosure (ZMod 2)) V) := by
        rw [hsub]; trivial
      exact hv (by simpa [Submodule.mem_bot] using hvmem)
    haveI : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot_top⟩⟩
    have hnot : ¬ (∀ a : Subrepresentation ρ, a = ⊥ ∨ a = ⊤) := by
      intro hall
      exact hirr ((isSimpleOrder_iff (Subrepresentation ρ)).mpr ⟨inferInstance, hall⟩)
    push Not at hnot
    obtain ⟨σ, hσbot, hσtop⟩ := hnot
    have hσsub_bot : σ.toSubmodule ≠ ⊥ := by
      intro h
      exact hσbot (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
    have hσsub_top : σ.toSubmodule ≠ ⊤ := by
      intro h
      exact hσtop (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
    haveI : Nontrivial σ.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hσsub_bot
    haveI : Module.Finite (AlgebraicClosure (ZMod 2)) σ.toSubmodule := inferInstance
    have hlt : Module.finrank (AlgebraicClosure (ZMod 2)) σ.toSubmodule < n := by
      rw [← hfin]
      exact Submodule.finrank_lt hσsub_top
    obtain ⟨w, hw, hwe⟩ :=
      ih (Module.finrank (AlgebraicClosure (ZMod 2)) σ.toSubmodule) hlt σ.toSubmodule
        σ.toRepresentation rfl
    refine ⟨(w : V), fun h => hw ?_, ?_⟩
    · exact Subtype.ext h
    · exact (Subrepresentation.toRepresentation_apply_coe (ρ' := σ) (g := e) (v := w)
        (w := w)).mp hwe

private theorem exists_fixed_vector_over_zmod_two {Γ : Type} [Group Γ] [Finite Γ] (e : Γ)
    (hW : ∀ (W : Type) [AddCommGroup W] [Module (AlgebraicClosure (ZMod 2)) W]
      [Module.Finite (AlgebraicClosure (ZMod 2)) W]
      (ρ : Representation (AlgebraicClosure (ZMod 2)) Γ W)
      [IsSimpleModule (MonoidAlgebra (AlgebraicClosure (ZMod 2)) Γ) ρ.asModule],
      ∃ w : W, w ≠ 0 ∧ ρ e w = w)
    (A : Type) [AddCommGroup A] [Module (ZMod 2) A] [Module.Finite (ZMod 2) A] [Nontrivial A]
    (ρ : Representation (ZMod 2) Γ A) : ∃ a : A, a ≠ 0 ∧ ρ e a = a := by
  let K := AlgebraicClosure (ZMod 2)
  let V := K ⊗[ZMod 2] A
  haveI hFin : Module.Finite K V := Module.Finite.base_change (ZMod 2) K A
  haveI hTors : Module.IsTorsionFree K V := inferInstance
  haveI hFlat : Module.Flat (ZMod 2) K := Module.Flat.of_free
  haveI hNontriv : Nontrivial V := by
    rw [← Module.finrank_pos_iff (R := K)]
    rw [Module.finrank_baseChange]
    exact (Module.finrank_pos_iff (R := ZMod 2) (M := A)).mpr ‹Nontrivial A›
  let ρK : Representation K Γ V :=
    { toFun := fun g => LinearMap.baseChange K (ρ g)
      map_one' := by rw [map_one, LinearMap.baseChange_one]
      map_mul' := by
        intro g h
        rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
        exact LinearMap.baseChange_comp (ρ h) (ρ g) }
  obtain ⟨v, hv0, hve⟩ :=
    exists_fixed_vector_of_simple (Γ := Γ) e hW (Module.finrank K V) V ρK rfl
  let f : A →ₗ[ZMod 2] A := ρ e - 1
  have hbase : LinearMap.baseChange K f = LinearMap.baseChange K (ρ e) - 1 := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]
  have hvker : LinearMap.baseChange K f v = 0 := by
    rw [hbase, LinearMap.sub_apply, Module.End.one_apply]
    change (ρK e) v - v = 0
    rw [hve, sub_self]
  have hfnot : ¬ Function.Injective f := by
    intro hf
    have hfb : Function.Injective (LinearMap.baseChange K f) := by
      have h := Module.Flat.lTensor_preserves_injective_linearMap (M := K) f hf
      simpa only [LinearMap.baseChange_eq_ltensor] using h
    exact hv0 (hfb (by rw [hvker, map_zero]))
  have hker : f.ker ≠ ⊥ := fun h => hfnot ((LinearMap.ker_eq_bot (f := f)).mp h)
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff f.ker).mp hker
  refine ⟨a, ha0, ?_⟩
  have hfa : f a = 0 := ha
  have : ρ e a - a = 0 := by
    simpa only [f, LinearMap.sub_apply, Module.End.one_apply] using hfa
  exact sub_eq_zero.mp this

theorem fixed_vector_descent {Γ : Type} [Group Γ] [Finite Γ] (e : Γ) (hodd : Odd (orderOf e))
    (hW : ∀ (W : Type) [AddCommGroup W] [Module (AlgebraicClosure (ZMod 2)) W]
      [Module.Finite (AlgebraicClosure (ZMod 2)) W]
      (ρ : Representation (AlgebraicClosure (ZMod 2)) Γ W)
      [IsSimpleModule (MonoidAlgebra (AlgebraicClosure (ZMod 2)) Γ) ρ.asModule],
      ∃ w : W, w ≠ 0 ∧ ρ e w = w)
    (Q : Type) [Group Q] [Finite Q] (hQ : ∀ x : Q, x ^ 2 = 1) [Nontrivial Q]
    (ρ : Γ →* MulAut Q)
    (hirr : ∀ W : Subgroup Q, (∀ r, ∀ x ∈ W, ρ r x ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ x : Q, x ≠ 1 ∧ ρ e x = x := by
  have hcomm : ∀ x y : Q, x * y = y * x := commute_of_sq_eq_one hQ
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  have h2smul : ∀ x : Additive Q, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    rw [show x + x = Additive.ofMul (Additive.toMul x * Additive.toMul x) from rfl]
    rw [show Additive.toMul x * Additive.toMul x = 1 from by
      simpa [pow_two] using hQ (Additive.toMul x)]
    rfl
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule h2smul
  haveI : Finite (Additive Q) := inferInstance
  haveI : Module.Finite (ZMod 2) (Additive Q) := Module.Finite.of_finite
  haveI : Nontrivial (Additive Q) := inferInstance
  let ρ' : Representation (ZMod 2) Γ (Additive Q) :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap 2 ((ρ g).toAdditive.toAddMonoidHom)
      map_one' := by
        ext x
        simp [AddMonoidHom.coe_toZModLinearMap]
      map_mul' := by
        intro g h
        ext x
        simp [AddMonoidHom.coe_toZModLinearMap] }
  obtain ⟨a, ha0, hae⟩ := exists_fixed_vector_over_zmod_two (Γ := Γ) e hW (Additive Q) ρ'
  refine ⟨Additive.toMul a, ?_, ?_⟩
  · intro h
    apply ha0
    apply Additive.toMul.injective
    rw [h]
    rfl
  · have hh := congrArg Additive.toMul hae
    simpa [ρ'] using hh

end Ree

end CFSG.StandardType
