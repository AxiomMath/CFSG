module

public import CFSG.LocalAnalysis.ZStar.TwoAdicWedderburn

public section

namespace CFSG

namespace ZStar.TwoAdicOrthogonality

open ZStar.GroupAlgebraTwistedTrace
open ZStar.PadicBlockField
open ZStar.PadicBlockProperties
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnBlock

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {G : Type v} [Group G] [Fintype G]

private theorem trace_mulLeftRight_single_mul_central
    [DecidableEq G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (e : MonoidAlgebra K G)
    (hecentral : e ∈ Submonoid.center (MonoidAlgebra K G)) :
    LinearMap.trace K (MonoidAlgebra K G)
        (LinearMap.mulLeftRight K
          (MonoidAlgebra.single a 1, MonoidAlgebra.single b 1 * e)) =
      ∑ g : G, e.coeff (g⁻¹ * a * g * b⁻¹) := by
  let β : Module.Basis G K (MonoidAlgebra K G) := MonoidAlgebra.basis G K
  rw [LinearMap.trace_eq_matrix_trace K β]
  change (∑ g : G,
    ((LinearMap.toMatrix β β)
      (LinearMap.mulLeftRight K
        (MonoidAlgebra.single a 1, MonoidAlgebra.single b 1 * e))) g g) = _
  apply Finset.sum_congr rfl
  intro g hg
  rw [LinearMap.toMatrix_apply]
  change (β.repr
    ((LinearMap.mulLeftRight K
      (MonoidAlgebra.single a 1, MonoidAlgebra.single b 1 * e)) (β g))) g = _
  rw [show β g = MonoidAlgebra.single g 1 by
    exact MonoidAlgebra.basis_apply K g]
  change ((LinearMap.mulLeftRight K
      (MonoidAlgebra.single a 1, MonoidAlgebra.single b 1 * e))
        (MonoidAlgebra.single g 1)).coeff g = _
  rw [LinearMap.mulLeftRight_apply]
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul,
    MonoidAlgebra.coeff_single_mul_apply, one_mul]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc
    e.coeff ((a * g * b)⁻¹ * g) =
        e.coeff (b * (g⁻¹ * a * g * b⁻¹) * b⁻¹) := by
      congr 1
      rw [mul_inv_rev, mul_inv_rev, hainv, hbinv]
      calc
        b * (g⁻¹ * a) * g = (b * (g⁻¹ * a) * g) * 1 := by simp
        _ = (b * (g⁻¹ * a) * g) * (b * b) := by rw [hb]
        _ = b * (g⁻¹ * a * g * b) * b := by group
    _ = e.coeff (g⁻¹ * a * g * b⁻¹) :=
      coeff_conj_eq_of_mem_center hecentral b _

private theorem sum_principalBlockTwoAdic_coeff_twoSidedTwist_eq_zero
    [DecidableEq G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hnconj : ¬IsConj a b) :
    (∑ g : G,
      (principalBlockTwoAdic (G := G)).coeff
        (g⁻¹ * a * g * b⁻¹)) = 0 := by
  have h := congrArg padicIntToComplex
    (sum_principalBlockPadic_coeff_twoSidedTwist_eq_zero
      (G := G) a b ha hb hnconj)
  rw [map_sum, map_zero] at h
  simpa only [principalBlockTwoAdic,
    MonoidAlgebra.coeff_mapRingHom] using h

private theorem trace_principalBlockTwoAdic_mulLeftRight_eq_zero
    [DecidableEq G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hnconj : ¬IsConj a b) :
    LinearMap.trace TwoAdicComplex (MonoidAlgebra TwoAdicComplex G)
        (LinearMap.mulLeftRight TwoAdicComplex
          (MonoidAlgebra.single a 1,
            MonoidAlgebra.single b 1 * principalBlockTwoAdic (G := G))) = 0 := by
  rw [trace_mulLeftRight_single_mul_central a b ha hb
    (principalBlockTwoAdic (G := G)) principalBlockTwoAdic_central]
  exact sum_principalBlockTwoAdic_coeff_twoSidedTwist_eq_zero
    a b ha hb hnconj

theorem principalBlock_component_orthogonality
    [DecidableEq G]
    (D : Decomposition G)
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hnconj : ¬IsConj a b) :
    (∑ i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := G)),
      (componentRepresentation D i).character a *
        (componentRepresentation D i).character b) = 0 := by
  calc
    (∑ i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := G)),
      (componentRepresentation D i).character a *
        (componentRepresentation D i).character b) =
        ∑ i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := G)),
          Matrix.trace (D.equiv (MonoidAlgebra.single a 1) i) *
            Matrix.trace (D.equiv (MonoidAlgebra.single b 1) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [componentCharacter_eq_matrixTrace,
        componentCharacter_eq_matrixTrace]
    _ = LinearMap.trace TwoAdicComplex (MonoidAlgebra TwoAdicComplex G)
        (LinearMap.mulLeftRight TwoAdicComplex
          (MonoidAlgebra.single a 1,
            MonoidAlgebra.single b 1 * principalBlockTwoAdic (G := G))) := by
      symm
      exact trace_mulLeftRight_mul_centralIdempotent
        D.equiv (principalBlockTwoAdic (G := G))
        principalBlockTwoAdic_central principalBlockTwoAdic_idempotent
        (MonoidAlgebra.single a 1) (MonoidAlgebra.single b 1)
    _ = 0 := trace_principalBlockTwoAdic_mulLeftRight_eq_zero
      a b ha hb hnconj

end

end ZStar.TwoAdicOrthogonality

end CFSG
