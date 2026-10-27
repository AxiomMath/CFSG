module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne.AUTSL

open Module Module.End Matrix

section Gen

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [Field k]

theorem exists_conj_diagonal_gen {ζ : k} (hζ : IsPrimitiveRoot ζ 5) {G : Type*} [CommGroup G]
    [Finite G] (hG5 : ∀ x : G, x ^ 5 = 1) (ρ : G →* Matrix ι ι k) :
    ∃ P : GL ι k, ∀ g : G,
      ((P : Matrix ι ι k) * ρ g * ((P⁻¹ : GL ι k) : Matrix ι ι k)).IsDiag := by
  classical
  let f : G → End k (ι → k) := fun g => Matrix.toLinAlgEquiv' (ρ g)
  have hcomm : ∀ x y, Commute (f x) (f y) := fun x y => by
    show f x * f y = f y * f x
    simp only [f, ← map_mul, ← map_mul ρ, mul_comm]
  have hpow : ∀ x, f x ^ 5 = 1 := fun x => by
    simp only [f, ← map_pow, ← map_pow ρ, hG5, map_one]
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ f hcomm hpow
  let e : ι ≃ Fin (finrank k (ι → k)) :=
    (Fintype.equivFin ι).trans (finCongr (Module.finrank_fintype_fun_eq_card k).symm)
  let b' : Basis ι k (ι → k) := b.reindex e.symm
  have hb' : ∀ (g : G) (j : ι), (ρ g) *ᵥ (b' j) = μ g (e j) • b' j := fun g j => by
    have := hb g (e j)
    simpa [f, b', Basis.reindex_apply] using this
  let P : Matrix ι ι k := (Pi.basisFun k ι).toMatrix b'
  have hPi : Invertible P := Basis.invertibleToMatrix (Pi.basisFun k ι) b'
  let Pu : GL ι k := unitOfInvertible P
  refine ⟨Pu⁻¹, fun g i j hij => ?_⟩
  have hxP : ρ g * P = P * Matrix.diagonal (fun j => μ g (e j)) := by
    ext a j
    have h := congrFun (hb' g j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [P, Matrix.mul_apply, Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
  have h1 : ((Pu⁻¹ : GL ι k) : Matrix ι ι k) = ⅟P := rfl
  have h2 : (((Pu⁻¹)⁻¹ : GL ι k) : Matrix ι ι k) = P := by simp [Pu]
  have h3 : ((Pu⁻¹ : GL ι k) : Matrix ι ι k) * ρ g * (((Pu⁻¹)⁻¹ : GL ι k) : Matrix ι ι k) =
      Matrix.diagonal (fun j => μ g (e j)) := by
    rw [h1, h2, Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
  show (((Pu⁻¹ : GL ι k) : Matrix ι ι k) * ρ g * (((Pu⁻¹)⁻¹ : GL ι k) : Matrix ι ι k)) i j = 0
  rw [h3]
  exact Matrix.diagonal_apply_ne _ hij

theorem exists_characters_gen {ζ : k} (hζ : IsPrimitiveRoot ζ 5) {G : Type*} [CommGroup G]
    [Finite G] (hG5 : ∀ x : G, x ^ 5 = 1) (ρ : G →* Matrix ι ι k) :
    ∃ (P : GL ι k) (f : ι → (G →* kˣ)), ∀ g : G,
      (P : Matrix ι ι k) * ρ g * ((P⁻¹ : GL ι k) : Matrix ι ι k) =
        Matrix.diagonal fun i => ((f i g : kˣ) : k) := by
  classical
  obtain ⟨P, hP⟩ := exists_conj_diagonal_gen hζ hG5 ρ
  set Dm : G → Matrix ι ι k := fun g =>
    (P : Matrix ι ι k) * ρ g * ((P⁻¹ : GL ι k) : Matrix ι ι k) with hDm
  have hdiag : ∀ g, (Dm g).IsDiag := hP
  have hmul : ∀ g h, Dm (g * h) = Dm g * Dm h := fun g h => by
    simp only [hDm, map_mul]
    calc (P : Matrix ι ι k) * (ρ g * ρ h) * ((P⁻¹ : GL ι k) : Matrix ι ι k)
        = (P : Matrix ι ι k) * ρ g * (((P⁻¹ : GL ι k) : Matrix ι ι k) * (P : Matrix ι ι k)) *
          ρ h * ((P⁻¹ : GL ι k) : Matrix ι ι k) := by
          rw [Units.inv_mul, mul_one]; noncomm_ring
      _ = _ := by noncomm_ring
  have hone : Dm 1 = 1 := by
    simp only [hDm, map_one, mul_one]
    exact Units.mul_inv P
  let fm : ι → (G →* k) := fun i =>
    { toFun := fun g => Dm g i i
      map_one' := by rw [hone, Matrix.one_apply_eq]
      map_mul' := fun g h => by
        rw [hmul, Matrix.mul_apply, Finset.sum_eq_single i]
        · intro l _ hli
          rw [hdiag g (Ne.symm hli), zero_mul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi }
  refine ⟨P, fun i => (fm i).toHomUnits, fun g => ?_⟩
  have h1 : (Dm g) = Matrix.diagonal fun i => Dm g i i := ((hdiag g).diagonal_diag).symm
  show Dm g = Matrix.diagonal fun i => (((fm i).toHomUnits g : kˣ) : k)
  rw [h1]
  congr 1

end Gen

end CFSG.RankThree.PartOne.AUTSL
