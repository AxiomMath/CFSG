module

public import TauCeti.RingTheory.FiniteType.PointSeparation

public noncomputable section

namespace CFSG

universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem moduleFinite_of_finite_algHom (A : Type v) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Finite (A →ₐ[k] k)] : Module.Finite k A := by
  classical
  let : Fintype (A →ₐ[k] k) := Fintype.ofFinite _
  let : Algebra.IsIntegral k A := ⟨fun a => by
    let s : Finset k := insert 0 (Finset.univ.image fun f : A →ₐ[k] k => f a)
    let P : Polynomial k := ∏ y ∈ s, (Polynomial.X - Polynomial.C y)
    have hmonic : P.Monic := Polynomial.monic_prod_of_monic _ _
      (fun y _ => Polynomial.monic_X_sub_C y)
    have hdegree : P.natDegree = s.card := by
      rw [Polynomial.natDegree_prod_of_monic s (fun y => Polynomial.X - Polynomial.C y)
        (fun y _ => Polynomial.monic_X_sub_C y)]
      simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    have hpositive : P.natDegree ≠ 0 := by
      rw [hdegree]
      exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩)
    have hnil : IsNilpotent (Polynomial.aeval a P) := by
      apply (TauCeti.forall_algHom_apply_eq_zero_iff_isNilpotent (k := k) (K := k) _).1
      intro f
      rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def, Algebra.algebraMap_self,
        Polynomial.eval₂_id]
      change Polynomial.eval (f a) (∏ y ∈ s, (Polynomial.X - Polynomial.C y)) = 0
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (i := f a)
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩)
      · simp
    obtain ⟨n, hn⟩ := hnil
    apply IsIntegral.of_aeval_monic hmonic hpositive
    apply IsIntegral.of_pow (n := n + 1) (by omega)
    rw [pow_succ, hn, zero_mul]
    exact isIntegral_zero⟩
  exact Algebra.IsIntegral.finite

end CFSG
