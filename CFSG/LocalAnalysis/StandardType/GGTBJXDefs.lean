module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LocalAnalysis.StandardType.GGTBJReflLemma
public import Mathlib.LinearAlgebra.Reflection

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley

@[expose] def ggTBJXa (p : ℕ) {K : Type} [Field K] (τ : Tag) (ζ : Kˣ)
    (f : Multiplicative (Fin τ.rank → ZMod p)) : Fin τ.rank → Kˣ :=
  fun i => ζ ^ (Multiplicative.toAdd f i).val

open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
@[expose] def GGTBJXStd (p : ℕ) (τ : Tag) {K : Type} [Field K] (ζ : Kˣ) {L' : Type} [Group L']
    (ψ : L' →* ModGL τ K) (σ : Multiplicative (Fin τ.rank → ZMod p) →* L') : Prop :=
  ψ.ker ≤ Subgroup.center L' ∧ ψ.range = adjointGroup τ K ∧ orderOf ζ = p ∧
    ∀ f : Multiplicative (Fin τ.rank → ZMod p), ψ (σ f) = rootDiagUnit τ (ggTBJXa p τ ζ f)

@[expose] noncomputable def ggTBJXFun (p : ℕ) [Fact p.Prime] (τ : Tag) (β : Fin τ.rank → ℤ) :
    Module.Dual (ZMod p) (Fin τ.rank → ZMod p) where
  toFun w := ∑ i : Fin τ.rank, (β i : ZMod p) * w i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' m x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem ggTBJXFun_apply (p : ℕ) [Fact p.Prime] (τ : Tag) (β : Fin τ.rank → ℤ)
    (w : Fin τ.rank → ZMod p) : ggTBJXFun p τ β w = ∑ i : Fin τ.rank, (β i : ZMod p) * w i :=
  rfl

open CFSG.LieType.Chevalley in
@[expose] def ggTBJXVec (p : ℕ) (τ : Tag) (β : Fin τ.rank → ℤ) : Fin τ.rank → ZMod p :=
  fun i => (corootPair (τ := τ) β (Pi.single i 1) : ZMod p)

theorem ggTBJXFun_add (p : ℕ) [Fact p.Prime] (τ : Tag) (β : Fin τ.rank → ℤ)
    (x y : Fin τ.rank → ZMod p) :
    ggTBJXFun p τ β (x + y) = ggTBJXFun p τ β x + ggTBJXFun p τ β y := by
  simp only [ggTBJXFun_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem ggTBJXAux_sum {R : Type} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (v w : Fin n → R)
    (h : ∑ i : Fin n, (β i : R) * v i = 2) :
    ∑ i : Fin n, (β i : R) * (w i - (∑ j : Fin n, (β j : R) * w j) * v i) =
      - ∑ i : Fin n, (β i : R) * w i := by
  have e : ∀ i, (β i : R) * (w i - (∑ j : Fin n, (β j : R) * w j) * v i) =
      (β i : R) * w i - (∑ j : Fin n, (β j : R) * w j) * ((β i : R) * v i) := fun i => by ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, h]
  ring

private theorem ggTBJXAux_inv {R : Type} [CommRing R] (a x v : R) : a - x * v - (-x) * v = a := by
  ring

private theorem ggTBJXAux_add {R : Type} [CommRing R] (a b x y v : R) :
    a + b - (x + y) * v = (a - x * v) + (b - y * v) := by
  ring

theorem ggTBJXFun_sub_smul_vec (p : ℕ) [Fact p.Prime] (τ : Tag) {β : Fin τ.rank → ℤ}
    (h : ggTBJXFun p τ β (ggTBJXVec p τ β) = 2) (w : Fin τ.rank → ZMod p) :
    ggTBJXFun p τ β (fun i => w i - ggTBJXFun p τ β w * ggTBJXVec p τ β i) =
      - ggTBJXFun p τ β w := by
  have h' : ∑ i : Fin τ.rank, (β i : ZMod p) * ggTBJXVec p τ β i = 2 := h
  rw [ggTBJXFun_apply, ggTBJXFun_apply]
  exact ggTBJXAux_sum β (ggTBJXVec p τ β) w h'

@[expose] noncomputable def ggTBJXReflAut (p : ℕ) [Fact p.Prime] (τ : Tag) (β : Fin τ.rank → ℤ) :
    MulAut (Multiplicative (Fin τ.rank → ZMod p)) :=
  haveI := Classical.propDecidable (ggTBJXFun p τ β (ggTBJXVec p τ β) = 2)
  if h : ggTBJXFun p τ β (ggTBJXVec p τ β) = 2 then
    { toFun := fun f => Multiplicative.ofAdd (fun i => Multiplicative.toAdd f i -
        ggTBJXFun p τ β (Multiplicative.toAdd f) * ggTBJXVec p τ β i)
      invFun := fun f => Multiplicative.ofAdd (fun i => Multiplicative.toAdd f i -
        ggTBJXFun p τ β (Multiplicative.toAdd f) * ggTBJXVec p τ β i)
      left_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_ofAdd]
        rw [ggTBJXFun_sub_smul_vec p τ h]
        exact ggTBJXAux_inv _ _ _
      right_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_ofAdd]
        rw [ggTBJXFun_sub_smul_vec p τ h]
        exact ggTBJXAux_inv _ _ _
      map_mul' := fun f g => by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply]
        rw [ggTBJXFun_add]
        exact ggTBJXAux_add _ _ _ _ _ }
  else 1

theorem ggTBJXReflAut_apply (p : ℕ) [Fact p.Prime] (τ : Tag) {β : Fin τ.rank → ℤ}
    (h : ggTBJXFun p τ β (ggTBJXVec p τ β) = 2) (f : Multiplicative (Fin τ.rank → ZMod p))
    (i : Fin τ.rank) :
    Multiplicative.toAdd (ggTBJXReflAut p τ β f) i = Multiplicative.toAdd f i -
      ggTBJXFun p τ β (Multiplicative.toAdd f) * ggTBJXVec p τ β i := by
  rw [ggTBJXReflAut, dif_pos h]
  rfl

end CFSG.StandardType

end
