module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.Continuity.Init

public noncomputable section

namespace CFSG

open scoped TensorProduct

universe u v w

private theorem aux_exists_algHom_ker_eq (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] : ∃ x : A →ₐ[k] k, RingHom.ker x = m := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have : Algebra.IsIntegral k (A ⧸ m) := Algebra.IsIntegral.of_finite k (A ⧸ m)
  have hbij : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext a
  simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  constructor
  · intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg e h
    simpa using this
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h]
    simp

private theorem aux_eq_zero_of_forall_algHom (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
    (a : A) (h : ∀ x : A →ₐ[k] k, x a = 0) : a = 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hmem : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨x, hx⟩ := aux_exists_algHom_ker_eq k A m
    rw [← hx]
    exact h x
  rw [← Ideal.radical_eq_jacobson, Ideal.mem_radical_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero a ⟨n, Ideal.mem_bot.1 hn⟩

private theorem aux_productMap_eq_sum (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A]
    (B : Type w) [CommRing B] [Algebra k B]
    {ι : Type*} (b : Module.Basis ι k B) (f : A ⊗[k] B) (x : A →ₐ[k] k) (y : B →ₐ[k] k) :
    Algebra.TensorProduct.productMap x y f =
      y (((Algebra.TensorProduct.basis A b).repr f).sum fun i c => x c • b i) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis A b).linearCombination_repr f]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, Algebra.smul_def,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul, Algebra.TensorProduct.productMap_apply_tmul, map_smul, smul_eq_mul]
  simp

theorem isDomain_tensorProduct_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsDomain A]
    (B : Type w) [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsDomain B] :
    IsDomain (A ⊗[k] B) := by
  classical
  let b := Module.Basis.ofVectorSpace k B
  have hspec : ∀ f g : A ⊗[k] B, f ≠ 0 → g ≠ 0 → ∃ x : A →ₐ[k] k,
      ((Algebra.TensorProduct.basis A b).repr f).sum (fun i c => x c • b i) ≠ 0 ∧
      ((Algebra.TensorProduct.basis A b).repr g).sum (fun i c => x c • b i) ≠ 0 := by
    intro f g hf hg
    obtain ⟨i, hi⟩ : ∃ i, (Algebra.TensorProduct.basis A b).repr f i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hf
      rw [← (Algebra.TensorProduct.basis A b).repr.map_eq_zero_iff]
      ext i
      exact hall i
    obtain ⟨j, hj⟩ : ∃ j, (Algebra.TensorProduct.basis A b).repr g j ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hg
      rw [← (Algebra.TensorProduct.basis A b).repr.map_eq_zero_iff]
      ext j
      exact hall j
    obtain ⟨x, hx⟩ : ∃ x : A →ₐ[k] k, x ((Algebra.TensorProduct.basis A b).repr f i *
        (Algebra.TensorProduct.basis A b).repr g j) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact mul_ne_zero hi hj (aux_eq_zero_of_forall_algHom k A _ hall)
    rw [map_mul] at hx
    refine ⟨x, fun h0 => ?_, fun h0 => ?_⟩
    · rw [Finsupp.sum] at h0
      exact left_ne_zero_of_mul hx ((linearIndependent_iff'.1 b.linearIndependent) _ _ h0 i
        (Finsupp.mem_support_iff.2 hi))
    · rw [Finsupp.sum] at h0
      exact right_ne_zero_of_mul hx ((linearIndependent_iff'.1 b.linearIndependent) _ _ h0 j
        (Finsupp.mem_support_iff.2 hj))
  have : Nontrivial (A ⊗[k] B) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨n, hn⟩ := Ideal.exists_maximal B
    obtain ⟨x, -⟩ := aux_exists_algHom_ker_eq k A m
    obtain ⟨y, -⟩ := aux_exists_algHom_ker_eq k B n
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have := congrArg (Algebra.TensorProduct.productMap x y) h
    rw [map_one, map_zero] at this
    exact one_ne_zero this
  have : NoZeroDivisors (A ⊗[k] B) := ⟨fun {f g} hfg => by
    by_contra hne
    push Not at hne
    obtain ⟨x, hfx, hgx⟩ := hspec f g hne.1 hne.2
    obtain ⟨y, hy⟩ : ∃ y : B →ₐ[k] k,
        y ((((Algebra.TensorProduct.basis A b).repr f).sum fun i c => x c • b i) *
          (((Algebra.TensorProduct.basis A b).repr g).sum fun i c => x c • b i)) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact mul_ne_zero hfx hgx (aux_eq_zero_of_forall_algHom k B _ hall)
    apply hy
    rw [map_mul, ← aux_productMap_eq_sum, ← aux_productMap_eq_sum, ← map_mul, hfg, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

end CFSG
