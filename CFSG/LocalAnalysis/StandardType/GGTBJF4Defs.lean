module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LocalAnalysis.StandardType.GGTBJReflLemma
public import Mathlib.LinearAlgebra.Reflection

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley in
@[expose] def ggTBJa (p : ℕ) {K : Type} [Field K] (ζ : Kˣ) (f : Multiplicative (Fin 4 → ZMod p)) :
    Fin Tag.F4.rank → Kˣ :=
  fun i => ζ ^ (Multiplicative.toAdd f i).val

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
@[expose] def GGTBJF4Std (p : ℕ) {K : Type} [Field K] (ζ : Kˣ) {L' : Type} [Group L']
    (ψ : L' →* ModGL Tag.F4 K) (σ : Multiplicative (Fin 4 → ZMod p) →* L') : Prop :=
  ψ.ker ≤ Subgroup.center L' ∧ ψ.range = adjointGroup Tag.F4 K ∧ orderOf ζ = p ∧
    ∀ f : Multiplicative (Fin 4 → ZMod p), ψ (σ f) = rootDiagUnit Tag.F4 (ggTBJa p ζ f)

@[expose] noncomputable def ggTBJFun (p : ℕ) [Fact p.Prime] (β : Fin 4 → ℤ) :
    Module.Dual (ZMod p) (Fin 4 → ZMod p) where
  toFun w := ∑ i : Fin 4, (β i : ZMod p) * w i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' m x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem ggTBJFun_apply (p : ℕ) [Fact p.Prime] (β : Fin 4 → ℤ) (w : Fin 4 → ZMod p) :
    ggTBJFun p β w = ∑ i : Fin 4, (β i : ZMod p) * w i :=
  rfl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
@[expose] def ggTBJVec (p : ℕ) (β : Fin 4 → ℤ) : Fin 4 → ZMod p :=
  fun i => (corootPair (τ := Tag.F4) β (Pi.single i 1) : ZMod p)

theorem ggTBJFun_add (p : ℕ) [Fact p.Prime] (β : Fin 4 → ℤ) (x y : Fin 4 → ZMod p) :
    ggTBJFun p β (x + y) = ggTBJFun p β x + ggTBJFun p β y := by
  simp only [ggTBJFun_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem ggTBJ_aux_sum {R : Type} [CommRing R] (β : Fin 4 → ℤ) (v w : Fin 4 → R)
    (h : ∑ i : Fin 4, (β i : R) * v i = 2) :
    ∑ i : Fin 4, (β i : R) * (w i - (∑ j : Fin 4, (β j : R) * w j) * v i) =
      - ∑ i : Fin 4, (β i : R) * w i := by
  have e : ∀ i, (β i : R) * (w i - (∑ j : Fin 4, (β j : R) * w j) * v i) =
      (β i : R) * w i - (∑ j : Fin 4, (β j : R) * w j) * ((β i : R) * v i) := fun i => by ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, h]
  ring

private theorem ggTBJ_aux_inv {R : Type} [CommRing R] (a x v : R) : a - x * v - (-x) * v = a := by
  ring

private theorem ggTBJ_aux_add {R : Type} [CommRing R] (a b x y v : R) :
    a + b - (x + y) * v = (a - x * v) + (b - y * v) := by
  ring

theorem ggTBJFun_sub_smul_vec (p : ℕ) [Fact p.Prime] {β : Fin 4 → ℤ}
    (h : ggTBJFun p β (ggTBJVec p β) = 2) (w : Fin 4 → ZMod p) :
    ggTBJFun p β (fun i => w i - ggTBJFun p β w * ggTBJVec p β i) = - ggTBJFun p β w := by
  have h' : ∑ i : Fin 4, (β i : ZMod p) * ggTBJVec p β i = 2 := h
  rw [ggTBJFun_apply, ggTBJFun_apply]
  exact ggTBJ_aux_sum β (ggTBJVec p β) w h'

@[expose] noncomputable def ggTBJReflAut (p : ℕ) [Fact p.Prime] (β : Fin 4 → ℤ) :
    MulAut (Multiplicative (Fin 4 → ZMod p)) :=
  haveI := Classical.propDecidable (ggTBJFun p β (ggTBJVec p β) = 2)
  if h : ggTBJFun p β (ggTBJVec p β) = 2 then
    { toFun := fun f => Multiplicative.ofAdd (fun i => Multiplicative.toAdd f i -
        ggTBJFun p β (Multiplicative.toAdd f) * ggTBJVec p β i)
      invFun := fun f => Multiplicative.ofAdd (fun i => Multiplicative.toAdd f i -
        ggTBJFun p β (Multiplicative.toAdd f) * ggTBJVec p β i)
      left_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_ofAdd]
        rw [ggTBJFun_sub_smul_vec p h]
        exact ggTBJ_aux_inv _ _ _
      right_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_ofAdd]
        rw [ggTBJFun_sub_smul_vec p h]
        exact ggTBJ_aux_inv _ _ _
      map_mul' := fun f g => by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply]
        rw [ggTBJFun_add]
        exact ggTBJ_aux_add _ _ _ _ _ }
  else 1

theorem ggTBJReflAut_apply (p : ℕ) [Fact p.Prime] {β : Fin 4 → ℤ}
    (h : ggTBJFun p β (ggTBJVec p β) = 2) (f : Multiplicative (Fin 4 → ZMod p)) (i : Fin 4) :
    Multiplicative.toAdd (ggTBJReflAut p β f) i = Multiplicative.toAdd f i -
      ggTBJFun p β (Multiplicative.toAdd f) * ggTBJVec p β i := by
  rw [ggTBJReflAut, dif_pos h]
  rfl

end CFSG.StandardType

end
