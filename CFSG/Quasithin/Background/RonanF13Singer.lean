module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RingTheory.LittleWedderburn

public section

namespace CFSG.Quasithin.RonanF13

open Algebra

section Aux

variable {V : Type*} [CommGroup V] [Module (ZMod 2) (Additive V)]

@[expose] noncomputable def toEnd (σ : MulAut V) : Module.End (ZMod 2) (Additive V) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun x => Additive.ofMul (σ (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun a b => by
        show Additive.ofMul (σ (Additive.toMul a * Additive.toMul b)) = _
        rw [map_mul]
        rfl }

theorem toEnd_apply (σ : MulAut V) (x : Additive V) :
    toEnd σ x = Additive.ofMul (σ (Additive.toMul x)) := rfl

theorem toEnd_mul (σ τ : MulAut V) : toEnd (σ * τ) = toEnd σ * toEnd τ := rfl

theorem toEnd_one : toEnd (1 : MulAut V) = 1 := rfl

theorem toEnd_injective : Function.Injective (toEnd : MulAut V → Module.End (ZMod 2) (Additive V)) := by
  intro σ τ h
  ext v
  have := congrArg (fun f => Additive.toMul (f (Additive.ofMul v))) h
  simpa [toEnd_apply] using this

end Aux

section Main

variable {Dg V : Type*} [CommGroup Dg] [CommGroup V] [Finite V]

theorem singer_frobenius [Nontrivial V] (hV2 : ∀ v : V, v * v = 1)
    (ρ : Dg →* MulAut V) (hρ : Function.Injective ρ)
    (hirr : ∀ W : Subgroup V, (∀ d, ∀ w ∈ W, ρ d w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ψ : MulAut Dg) (A : MulAut V) (hA : ∀ d v, A (ρ d v) = ρ (ψ d) (A v)) :
    IsCyclic Dg ∧ ∃ k : ℕ, ∀ d, ψ d = d ^ 2 ^ k := by
  classical
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero, sq]
    exact hV2 _
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  let ρE : Dg →* Module.End (ZMod 2) (Additive V) :=
    { toFun := fun d => toEnd (ρ d)
      map_one' := by simp [toEnd_one]
      map_mul' := fun a b => by simp [toEnd_mul] }
  have hρE : Function.Injective ρE := toEnd_injective.comp hρ
  let S : Set (Module.End (ZMod 2) (Additive V)) := Set.range ρE
  have hS : S.Pairwise Commute := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    show ρE a * ρE b = ρE b * ρE a
    rw [← map_mul, ← map_mul, mul_comm]
  let R : Subalgebra (ZMod 2) (Module.End (ZMod 2) (Additive V)) := adjoin (ZMod 2) S
  haveI hRcomm : IsMulCommutative R := Algebra.isMulCommutative_adjoin (ZMod 2) hS
  have hSR : ∀ d, ρE d ∈ R := fun d => Algebra.subset_adjoin ⟨d, rfl⟩
  haveI : Finite R := by
    have : Finite (Module.End (ZMod 2) (Additive V)) :=
      Finite.of_injective (fun f : Module.End (ZMod 2) (Additive V) =>
        (f : Additive V → Additive V)) DFunLike.coe_injective
    exact Finite.of_injective (fun r : R => (r : Module.End (ZMod 2) (Additive V))) Subtype.val_injective
  have hcomm : ∀ (e : R) (d : Dg), e.1 * ρE d = ρE d * e.1 := by
    intro e d
    have := (IsMulCommutative.is_comm (M := R)).comm (⟨ρE d, hSR d⟩ : R) e
    exact (congrArg Subtype.val this).symm
  have hinj : ∀ e : R, e ≠ 0 → Function.Injective e.1 := by
    intro e he
    rw [injective_iff_map_eq_zero]
    intro v hv
    let W : Subgroup V :=
      { carrier := {w | e.1 (Additive.ofMul w) = 0}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at *
          rw [ofMul_mul, map_add, ha, hb, add_zero]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at *
          rw [ofMul_inv, map_neg, ha, neg_zero] }
    have hWinv : ∀ d, ∀ w ∈ W, ρ d w ∈ W := by
      intro d w hw
      have hw' : e.1 (Additive.ofMul w) = 0 := hw
      show e.1 (Additive.ofMul (ρ d w)) = 0
      have h1 : Additive.ofMul (ρ d w) = ρE d (Additive.ofMul w) := rfl
      rw [h1, ← Module.End.mul_apply, hcomm e d, Module.End.mul_apply, hw', map_zero]
    rcases hirr W hWinv with h | h
    · have hv' : Additive.toMul v ∈ W := by
        show e.1 (Additive.ofMul (Additive.toMul v)) = 0
        simpa using hv
      rw [h] at hv'
      have : Additive.toMul v = 1 := hv'
      apply Additive.toMul.injective
      simpa using this
    · exfalso
      apply he
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      have hx : Additive.toMul x ∈ W := by rw [h]; trivial
      have : e.1 (Additive.ofMul (Additive.toMul x)) = 0 := hx
      simpa using this
  haveI : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    apply hb
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have h1 : a.1 (b.1 v) = 0 := by
      have := congrArg (fun r : R => r.1 v) hab
      simpa using this
    exact (injective_iff_map_eq_zero _).mp (hinj a ha) _ h1⟩
  haveI : IsDomain R := NoZeroDivisors.to_isDomain R
  have hF : IsField R := Finite.isDomain_to_isField R
  letI : Field R := hF.toField
  let Aℓ : Additive V ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofLinear (toEnd A) (toEnd A⁻¹)
      (by
        rw [← Module.End.mul_eq_comp, ← toEnd_mul, mul_inv_cancel, toEnd_one]
        rfl)
      (by
        rw [← Module.End.mul_eq_comp, ← toEnd_mul, inv_mul_cancel, toEnd_one]
        rfl)
  let c : Module.End (ZMod 2) (Additive V) ≃ₐ[ZMod 2] Module.End (ZMod 2) (Additive V) :=
    Aℓ.conjAlgEquiv (ZMod 2)
  have hc : ∀ d, c (ρE d) = ρE (ψ d) := by
    intro d
    apply LinearMap.ext
    intro x
    show Aℓ (ρE d (Aℓ.symm x)) = ρE (ψ d) x
    show Additive.ofMul (A (ρ d (A⁻¹ (Additive.toMul x)))) = Additive.ofMul (ρ (ψ d) (Additive.toMul x))
    rw [hA]
    simp
  have hmem : ∀ r : Module.End (ZMod 2) (Additive V), r ∈ R → c r ∈ R := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      rw [hc]
      exact hSR _
    | algebraMap a =>
      rw [AlgEquiv.commutes]
      exact R.algebraMap_mem a
    | add x y _ _ hx hy =>
      rw [map_add]
      exact R.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact R.mul_mem hx hy
  let β : R →ₐ[ZMod 2] R :=
    ((c : Module.End (ZMod 2) (Additive V) →ₐ[ZMod 2] Module.End (ZMod 2) (Additive V)).comp
      R.val).codRestrict R (fun r => hmem r.1 r.2)
  haveI : FiniteDimensional (ZMod 2) R := Module.Finite.of_finite
  have hβb : Function.Bijective β := AlgHom.bijective β
  let βe : R ≃ₐ[ZMod 2] R := AlgEquiv.ofBijective β hβb
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) R).2 βe
  refine ⟨?_, n.1, fun d => ?_⟩
  ·
    let f : Dg →* R :=
      { toFun := fun d => ⟨ρE d, hSR d⟩
        map_one' := Subtype.ext (map_one ρE)
        map_mul' := fun a b => Subtype.ext (map_mul ρE a b) }
    have hf : Function.Injective f := fun a b h => hρE (congrArg Subtype.val h)
    exact isCyclic_of_injective f.toHomUnits (fun a b h => hf (by simpa using congrArg Units.val h))
  apply hρE
  have key : ∀ y : R, βe y = y ^ 2 ^ n.1 := by
    intro y
    have h1 : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) R ^ n.1) y = βe y := by
      rw [← hn]
    rw [← h1, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp
  have h3 := congrArg Subtype.val (key ⟨ρE d, hSR d⟩)
  have h4 : (βe ⟨ρE d, hSR d⟩ : R).1 = ρE (ψ d) := hc d
  rw [h4] at h3
  rw [h3]
  simp [map_pow]

end Main

end CFSG.Quasithin.RonanF13
