module

public import CFSG.LocalAnalysis.ZStar.TwoAdicWedderburn
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG

namespace ZStar.CharacterKernel

open ZStar.TwoAdicWedderburn
open ZStar.PadicBlockField

noncomputable section

universe u

private theorem matrix_eq_one_of_mul_self_eq_one_of_trace_eq
    {K : Type u} [Field K] [CharZero K] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K)
    (hA2 : A * A = 1) (htrace : Matrix.trace A = (n : K)) :
    A = 1 := by
  let E : Matrix (Fin n) (Fin n) K :=
    (2 : K)⁻¹ • (1 - A)
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hsub2 :
      ((1 : Matrix (Fin n) (Fin n) K) - A) * (1 - A) =
        (2 : K) • (1 - A) := by
    calc
      (1 - A) * (1 - A) = 1 - A - A + A * A := by noncomm_ring
      _ = (2 : K) • (1 - A) := by
        rw [hA2]
        rw [two_smul K]
        noncomm_ring
  have hE2 : E * E = E := by
    dsimp only [E]
    rw [smul_mul_smul, hsub2, smul_smul]
    congr 1
    field_simp
  let e : Module.End K (Fin n → K) := Matrix.toLinAlgEquiv' E
  have he2 : IsIdempotentElem e := by
    rw [IsIdempotentElem, ← map_mul, hE2]
  have hetrace : LinearMap.trace K (Fin n → K) e = 0 := by
    change LinearMap.trace K (Fin n → K) (Matrix.toLin' E) = 0
    rw [Matrix.trace_toLin'_eq]
    dsimp only [E]
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, htrace]
    simp
  have hezero : e = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero he2 hetrace
  have hEzero : E = 0 := by
    exact Matrix.toLinAlgEquiv'.injective (by simpa [e] using hezero)
  dsimp only [E] at hEzero
  have hone_sub : (1 : Matrix (Fin n) (Fin n) K) - A = 0 := by
    exact (smul_eq_zero.mp hEzero).resolve_left (inv_ne_zero htwo)
  exact sub_eq_zero.mp hone_sub |>.symm

variable {G : Type u} [Group G] [Fintype G]

theorem component_eq_one_of_character_eq_degree
    (D : Decomposition G) (i : Fin D.blockCount) (t : G)
    (ht2 : t * t = 1)
    (hchar : (componentRepresentation D i).character t =
      (D.blockSize i : TwoAdicComplex)) :
    D.equiv (MonoidAlgebra.single t 1) i = 1 := by
  apply matrix_eq_one_of_mul_self_eq_one_of_trace_eq
  · rw [← Pi.mul_apply, ← map_mul,
      MonoidAlgebra.single_mul_single, ht2, one_mul,
      ← MonoidAlgebra.one_def, map_one]
    rfl
  · rw [componentCharacter_eq_matrixTrace] at hchar
    exact hchar

end

end ZStar.CharacterKernel

end CFSG
