module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenNormPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenNormTail

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow

variable {K : Type} [Field K] {β γ : K}

@[expose] def qaConj : QuadraticAlgebra K (-γ) β ≃ₐ[K] QuadraticAlgebra K (-γ) β where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_mul' x y := by rw [star_mul, mul_comm]
  map_add' := star_add
  commutes' r := by
    ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

theorem qaConj_apply (z : QuadraticAlgebra K (-γ) β) : qaConj z = star z :=
  rfl

section Bundle

variable [Finite K] [CharP K 2] [Fact (∀ r : K, r ^ 2 ≠ -γ + β * r)]

@[expose] noncomputable def qaNormForm (β γ : K) : QuadraticForm K (QuadraticAlgebra K (-γ) β) :=
  (binForm β γ).comp (qaEquiv β γ).toLinearMap

omit [Finite K] [CharP K 2] [Fact (∀ r : K, r ^ 2 ≠ -γ + β * r)] in
theorem qaNormForm_apply (z : QuadraticAlgebra K (-γ) β) :
    qaNormForm β γ z = QuadraticAlgebra.norm z := by
  rw [qaNormForm, QuadraticMap.comp_apply]
  exact binForm_qaEquiv z

@[expose] noncomputable def evenNormPlaneOfBin (hβ : β ≠ 0) :
    EvenNormPlane K (QuadraticAlgebra K (-γ) β) where
  σ := qaConj
  finrank_eq := by
    rw [(qaEquiv β γ).finrank_eq]
    simp
  σ_ne_one := fun h => hβ (by
    have := congrArg (fun φ : QuadraticAlgebra K (-γ) β ≃ₐ[K] QuadraticAlgebra K (-γ) β =>
      (φ (⟨0, 1⟩ : QuadraticAlgebra K (-γ) β)).re) h
    simpa [qaConj_apply, QuadraticAlgebra.re_star] using this)
  N := qaNormForm β γ
  algebraMap_N z := by
    rw [qaNormForm_apply, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    rfl

end Bundle

section Model

variable [Finite K] [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]

omit [Finite K] [CharP K 2] in
@[expose] noncomputable def minusCoordEquiv {m : ℕ} (b : Basis (Fin m ⊕ Fin m ⊕ Fin 2) K W) :
    W ≃ₗ[K] (((Fin m → K) × (Fin m → K)) × QuadraticAlgebra K (-γ) β) :=
  b.equivFun.trans <|
    (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin m ⊕ Fin 2) K K).trans <|
    ((LinearEquiv.refl K (Fin m → K)).prodCongr
      (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin 2) K K)).trans <|
    (LinearEquiv.prodAssoc K (Fin m → K) (Fin m → K) (Fin 2 → K)).symm.trans <|
    (LinearEquiv.refl K ((Fin m → K) × (Fin m → K))).prodCongr
      ((LinearEquiv.finTwoArrow K K).trans (qaEquiv β γ).symm)

omit [Finite K] [CharP K 2] in
theorem minusCoordEquiv_fst_fst {m : ℕ} (b : Basis (Fin m ⊕ Fin m ⊕ Fin 2) K W) (w : W)
    (i : Fin m) : (minusCoordEquiv (β := β) (γ := γ) b w).1.1 i = b.repr w (Sum.inl i) :=
  rfl

omit [Finite K] [CharP K 2] in
theorem minusCoordEquiv_fst_snd {m : ℕ} (b : Basis (Fin m ⊕ Fin m ⊕ Fin 2) K W) (w : W)
    (i : Fin m) : (minusCoordEquiv (β := β) (γ := γ) b w).1.2 i = b.repr w (Sum.inr (Sum.inl i)) :=
  rfl

omit [Finite K] [CharP K 2] in
theorem minusCoordEquiv_snd {m : ℕ} (b : Basis (Fin m ⊕ Fin m ⊕ Fin 2) K W) (w : W) :
    (minusCoordEquiv (β := β) (γ := γ) b w).2 =
      (qaEquiv β γ).symm (b.repr w (Sum.inr (Sum.inr 0)), b.repr w (Sum.inr (Sum.inr 1))) :=
  rfl

end Model

section Existence

variable [Finite K] [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_evenMinus_model (Q : QuadraticForm K W) (hQ : (polarBilin Q).Nondegenerate)
    {n : ℕ} (hn : 1 ≤ n) (hdim : finrank K W = 2 * n)
    (hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, Q u ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (D : EvenNormPlane K E)
      (ψ : W ≃ₗ[K] (((Fin (n - 1) → K) × (Fin (n - 1) → K)) × E)),
      ∀ w, evenNormTailForm D.N (n - 1) (ψ w) = Q w := by
  obtain ⟨-, -, hnf, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
      Q hQ
  rcases hnf n hn hdim with ⟨b, hb⟩ | ⟨β, γ, hβ, hirr, b, hb⟩
  · exfalso
    obtain ⟨u, hu, hu0⟩ := hts (Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)))
      ((finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp))
    apply hu0
    obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
    simpa using hb x 0
  · have : Fact (∀ r : K, r ^ 2 ≠ -γ + β * r) := ⟨noRoot_quadraticAlgebra hirr⟩
    refine ⟨QuadraticAlgebra K (-γ) β, inferInstance, inferInstance, evenNormPlaneOfBin hβ,
      minusCoordEquiv b, fun w => ?_⟩
    have hw := b.sum_repr w
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two] at hw
    have hw' : ∑ i, b.repr w (Sum.inl i) • b (Sum.inl i) +
        ∑ i, b.repr w (Sum.inr (Sum.inl i)) • b (Sum.inr (Sum.inl i)) +
        b.repr w (Sum.inr (Sum.inr 0)) • b (Sum.inr (Sum.inr 0)) +
        b.repr w (Sum.inr (Sum.inr 1)) • b (Sum.inr (Sum.inr 1)) = w := by
      refine Eq.trans ?_ hw
      abel
    have hQw := hb (fun i => b.repr w (Sum.inl i)) (fun i => b.repr w (Sum.inr (Sum.inl i)))
      (b.repr w (Sum.inr (Sum.inr 0))) (b.repr w (Sum.inr (Sum.inr 1)))
    rw [hw'] at hQw
    rw [hQw, evenNormTailForm_apply]
    change ∑ i, (minusCoordEquiv (β := β) (γ := γ) b w).1.1 i *
        (minusCoordEquiv (β := β) (γ := γ) b w).1.2 i +
        qaNormForm β γ ((minusCoordEquiv (β := β) (γ := γ) b w).2) = _
    rw [minusCoordEquiv_snd, qaNormForm, QuadraticMap.comp_apply]
    simp only [minusCoordEquiv_fst_fst, minusCoordEquiv_fst_snd]
    simp [binForm_apply]
    ring

end Existence

end CFSG.RankThree.PartOne.KCOrthogonal
