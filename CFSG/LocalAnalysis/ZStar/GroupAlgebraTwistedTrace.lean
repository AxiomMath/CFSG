module

public import CFSG.LocalAnalysis.ZStar.FixedPointFreeTrace
public import CFSG.LocalAnalysis.ZStar.ClassSums

public section

namespace CFSG

namespace ZStar.GroupAlgebraTwistedTrace

universe u v

variable {G : Type u} {R : Type v}

@[expose] def rightMulMatrix [Semiring R] [Group G]
    (e : MonoidAlgebra R G) : Matrix G G R :=
  fun g h => e.coeff (g⁻¹ * h)

@[simp]
theorem rightMulMatrix_apply [Semiring R] [Group G]
    (e : MonoidAlgebra R G) (g h : G) :
    rightMulMatrix e g h = e.coeff (g⁻¹ * h) := rfl

private theorem rightMulMatrix_mul [Semiring R] [Group G]
    [Fintype G] [DecidableEq G]
    (e₁ e₂ : MonoidAlgebra R G) :
    rightMulMatrix (e₁ * e₂) =
      rightMulMatrix e₁ * rightMulMatrix e₂ := by
  ext g h
  rw [Matrix.mul_apply]
  change (e₁ * e₂).coeff (g⁻¹ * h) =
    ∑ k : G, e₁.coeff (g⁻¹ * k) * e₂.coeff (k⁻¹ * h)
  rw [MonoidAlgebra.coeff_mul_apply_left]
  rw [Finsupp.sum_fintype]
  · symm
    apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
    intro k
    congr 2
    change k⁻¹ * h = (g⁻¹ * k)⁻¹ * (g⁻¹ * h)
    group
  · intro k
    simp

private theorem rightMulMatrix_idempotent [Semiring R] [Group G]
    [Fintype G] [DecidableEq G]
    (e : MonoidAlgebra R G) (he : e * e = e) :
    rightMulMatrix e * rightMulMatrix e = rightMulMatrix e := by
  rw [← rightMulMatrix_mul, he]

theorem coeff_conj_eq_of_mem_center [CommSemiring R] [Group G]
    {e : MonoidAlgebra R G}
    (he : e ∈ Submonoid.center (MonoidAlgebra R G))
    (g x : G) :
    e.coeff (g * x * g⁻¹) = e.coeff x := by
  apply ZStar.ClassSums.coeff_eq_of_isConj R he
  rw [isConj_iff]
  exact ⟨g⁻¹, by group⟩

private def twoSidedTwist [Group G] (a b : G) (g : G) : G :=
  a * g * b⁻¹

private theorem twoSidedTwist_involutive [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) :
    Function.Involutive (twoSidedTwist a b) := by
  intro g
  change a * (a * g * b⁻¹) * b⁻¹ = g
  calc
    a * (a * g * b⁻¹) * b⁻¹ = (a * a) * g * (b * b)⁻¹ := by group
    _ = g := by rw [ha, hb]; simp

private theorem twoSidedTwist_fixedPointFree [Group G] {a b : G}
    (hnconj : ¬IsConj a b) :
    ∀ g, twoSidedTwist a b g ≠ g := by
  intro g hfix
  apply hnconj
  apply IsConj.symm
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  calc
    g * b * g⁻¹ = twoSidedTwist a b g * b * g⁻¹ := by rw [hfix]
    _ = a := by simp only [twoSidedTwist]; group

private theorem rightMulMatrix_twoSidedTwist_invariant
    [CommSemiring R] [Group G]
    {e : MonoidAlgebra R G}
    (he : e ∈ Submonoid.center (MonoidAlgebra R G))
    (a b g h : G) :
    rightMulMatrix e (twoSidedTwist a b g) (twoSidedTwist a b h) =
      rightMulMatrix e g h := by
  change e.coeff
      ((a * g * b⁻¹)⁻¹ * (a * h * b⁻¹)) = e.coeff (g⁻¹ * h)
  apply ZStar.ClassSums.coeff_eq_of_isConj R he
  apply IsConj.symm
  rw [isConj_iff]
  exact ⟨b, by group⟩

private theorem trace_rightMulMatrix_mul_involutionMatrix
    [Group G] [Fintype G] [DecidableEq G]
    (f : G → G) (hf : Function.Involutive f)
    (e : MonoidAlgebra ℤ_[2] G) :
    Matrix.trace
        (rightMulMatrix e *
          ZStar.FixedPointFreeTrace.involutionMatrix f hf) =
      ∑ g : G, e.coeff (g⁻¹ * f g) := by
  have hdiag (g : G) :
      (rightMulMatrix e *
          ZStar.FixedPointFreeTrace.involutionMatrix f hf) g g =
        e.coeff (g⁻¹ * f g) := by
    unfold ZStar.FixedPointFreeTrace.involutionMatrix
    change Matrix.vecMul (rightMulMatrix e g) _ g = e.coeff (g⁻¹ * f g)
    rw [@Matrix.vecMul_permMatrix G ℤ_[2] (Classical.decEq G)
      (hf.toPerm f) _ (rightMulMatrix e g) _]
    rw [hf.toPerm_symm]
    rfl
  change
    (∑ g : G,
      (rightMulMatrix e *
        ZStar.FixedPointFreeTrace.involutionMatrix f hf) g g) = _
  simp_rw [hdiag]

private theorem trace_rightMulMatrix_mul_twoSidedTwist
    [Group G] [Fintype G] [DecidableEq G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (e : MonoidAlgebra ℤ_[2] G) :
    Matrix.trace
        (rightMulMatrix e *
          ZStar.FixedPointFreeTrace.involutionMatrix
            (twoSidedTwist a b) (twoSidedTwist_involutive ha hb)) =
      ∑ g : G, e.coeff (g⁻¹ * a * g * b⁻¹) := by
  rw [trace_rightMulMatrix_mul_involutionMatrix]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  simp only [twoSidedTwist]
  group

private theorem trace_rightMulMatrix_mul_twoSidedTwist_eq_zero
    [Group G] [Fintype G] [DecidableEq G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hnconj : ¬IsConj a b)
    (e : MonoidAlgebra ℤ_[2] G)
    (heidem : e * e = e)
    (hecentral : e ∈ Submonoid.center (MonoidAlgebra ℤ_[2] G)) :
    Matrix.trace
        (rightMulMatrix e *
          ZStar.FixedPointFreeTrace.involutionMatrix
            (twoSidedTwist a b) (twoSidedTwist_involutive ha hb)) = 0 := by
  apply ZStar.FixedPointFreeTrace.trace_mul_involutionMatrix_eq_zero
  · exact twoSidedTwist_fixedPointFree hnconj
  · exact rightMulMatrix_idempotent e heidem
  · exact rightMulMatrix_twoSidedTwist_invariant hecentral a b

theorem sum_coeff_twoSidedTwist_eq_zero
    [Group G] [Fintype G] [DecidableEq G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hnconj : ¬IsConj a b)
    (e : MonoidAlgebra ℤ_[2] G)
    (heidem : e * e = e)
    (hecentral : e ∈ Submonoid.center (MonoidAlgebra ℤ_[2] G)) :
    (∑ g : G, e.coeff (g⁻¹ * a * g * b⁻¹)) = 0 := by
  rw [← trace_rightMulMatrix_mul_twoSidedTwist a b ha hb e]
  exact trace_rightMulMatrix_mul_twoSidedTwist_eq_zero
    a b ha hb hnconj e heidem hecentral

end ZStar.GroupAlgebraTwistedTrace

end CFSG
