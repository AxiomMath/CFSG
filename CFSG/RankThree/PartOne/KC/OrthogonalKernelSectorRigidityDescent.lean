module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module TensorProduct CFSG.RankThree.PartOne.KCPrimary

section Descent

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem aeval_apply_mem_of_forall_mem {f : Module.End K V} {S : Submodule K V}
    (hS : ∀ v ∈ S, f v ∈ S) (p : K[X]) {v : V} (hv : v ∈ S) : aeval f p v ∈ S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact S.add_mem hp hq
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem c (Module.End.pow_apply_mem_of_forall_mem n hS v hv)

theorem inf_primaryComponent_ne_bot_of_eigenvector (L : Type) [Field L] [Algebra K L]
    {f : Module.End K V} {S : Submodule K V} (hS : ∀ v ∈ S, f v ∈ S) {μ : L}
    {s : L ⊗[K] V} (hsS : s ∈ S.baseChange L) (hs0 : s ≠ 0)
    (hsμ : f.baseChange L s = μ • s) : S ⊓ primaryComponent f (minpoly K μ) ≠ ⊥ := by
  set h := minpoly K μ with hh
  set F := aeval f h with hF
  have hFs : F.baseChange L s = 0 := by
    have h1 : F.baseChange L = aeval (f.baseChange L) h :=
      (Polynomial.aeval_algHom_apply (Module.End.baseChangeHom K L V) f h).symm
    rw [h1]
    have h2 := Module.End.aeval_apply_of_mem_apply_eq_smul (p := h.map (algebraMap K L)) hsμ
    rw [Polynomial.aeval_map_algebraMap, Polynomial.eval_map_algebraMap, hh,
      minpoly.aeval K μ, zero_smul] at h2
    exact h2
  have hFS : ∀ v ∈ S, F v ∈ S := fun v hv => aeval_apply_mem_of_forall_mem hS h hv
  intro hbot
  have hinj : Function.Injective (F.restrict hFS) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : F (v : V) = 0 := congrArg Subtype.val hv
    have h2 : (v : V) ∈ S ⊓ primaryComponent f h := ⟨v.2, mem_primaryComponent.mpr h1⟩
    rw [hbot] at h2
    exact Subtype.ext (Submodule.mem_bot K |>.mp h2)
  have hinjL : Function.Injective ((F.restrict hFS).baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  have hjL : Function.Injective (S.subtype.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ S.subtype_injective
  obtain ⟨u, rfl⟩ := hsS
  have hcomm : S.subtype ∘ₗ F.restrict hFS = F ∘ₗ S.subtype := by
    ext v
    rfl
  have h1 : S.subtype.baseChange L ((F.restrict hFS).baseChange L u) = 0 := by
    have := congrArg (fun m : S →ₗ[K] V => m.baseChange L u) hcomm
    simp only [LinearMap.baseChange_comp, LinearMap.coe_comp, Function.comp_apply] at this
    rw [this]
    exact hFs
  have h2 := hjL (h1.trans (map_zero _).symm)
  have h3 := hinjL (h2.trans (map_zero _).symm)
  exact hs0 (by rw [h3, map_zero])

end Descent

end CFSG.RankThree.PartOne.KCOrthogonal
