module

public import CFSG.RankThree.PartOne.N1322.Dihedral
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartOne.N1322

open Matrix Equiv

variable {K : Type*} [Field K]

@[expose] def IsRefl (g : GL (Fin 3) K) : Prop :=
  ∃ r φ : Fin 3 → K, r ≠ 0 ∧ φ ⬝ᵥ r = 2 ∧
    (g : Matrix (Fin 3) (Fin 3) K) = 1 - vecMulVec r φ

theorem IsRefl.mulVec_root {g : GL (Fin 3) K} {r φ : Fin 3 → K} (hφ : φ ⬝ᵥ r = 2)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = 1 - vecMulVec r φ) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ r = -r := by
  rw [hg, sub_mulVec, one_mulVec, vecMulVec_mulVec, hφ]
  simp [two_smul]

theorem IsRefl.mulVec_apply {g : GL (Fin 3) K} {r φ : Fin 3 → K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = 1 - vecMulVec r φ) (v : Fin 3 → K) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v - (φ ⬝ᵥ v) • r := by
  rw [hg, sub_mulVec, one_mulVec, vecMulVec_mulVec]
  simp

theorem IsRefl.sq {g : GL (Fin 3) K} (h : IsRefl g) : g * g = 1 := by
  obtain ⟨r, φ, hr, hφ, hg⟩ := h
  apply Units.ext
  have hNN : vecMulVec r φ * vecMulVec r φ = (2 : K) • vecMulVec r φ := by
    rw [vecMulVec_mul_vecMulVec, hφ, vecMulVec_smul]
  have h1 : (1 - vecMulVec r φ) * (1 - vecMulVec r φ) =
      1 - vecMulVec r φ - vecMulVec r φ + vecMulVec r φ * vecMulVec r φ := by noncomm_ring
  rw [Units.val_mul, hg, Units.val_one, h1, hNN, two_smul]
  abel

theorem IsRefl.trace_eq {g : GL (Fin 3) K} (h : IsRefl g) :
    Matrix.trace (g : Matrix (Fin 3) (Fin 3) K) = 3 - 2 := by
  obtain ⟨r, φ, hr, hφ, hg⟩ := h
  rw [hg, trace_sub, trace_one, trace_vecMulVec, dotProduct_comm, hφ]
  simp

theorem IsRefl.conj {g : GL (Fin 3) K} (h : IsRefl g) (P : GL (Fin 3) K) :
    IsRefl (P * g * P⁻¹) := by
  obtain ⟨r, φ, hr, hφ, hg⟩ := h
  refine ⟨(P : Matrix (Fin 3) (Fin 3) K) *ᵥ r, φ ᵥ* ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
    ?_, ?_, ?_⟩
  · intro h0
    apply hr
    have := congrArg (fun w => ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec] using this
  · rw [← dotProduct_mulVec, Matrix.mulVec_mulVec]
    simpa using hφ
  · rw [Units.val_mul, Units.val_mul, hg, mul_sub, sub_mul, mul_one, mul_vecMulVec, vecMulVec_mul]
    have : (P : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
      Units.mul_inv P
    rw [this]

theorem exists_vecMulVec_of_rank_one {N : Matrix (Fin 3) (Fin 3) K} (h : N.rank = 1) :
    ∃ r φ : Fin 3 → K, r ≠ 0 ∧ N = vecMulVec r φ := by
  have hfr : Module.finrank K (LinearMap.range N.mulVecLin) = 1 := h
  obtain ⟨v, hv0, hv⟩ := (finrank_eq_one_iff' (K := K) (V := LinearMap.range N.mulVecLin)).mp hfr
  have hmem : ∀ j : Fin 3, N *ᵥ Pi.single j (1 : K) ∈ LinearMap.range N.mulVecLin :=
    fun j => ⟨Pi.single j 1, rfl⟩
  choose φ hφ using fun j => hv ⟨N *ᵥ Pi.single j (1 : K), hmem j⟩
  refine ⟨(v : Fin 3 → K), φ, ?_, ?_⟩
  · intro h0
    exact hv0 (Subtype.ext h0)
  · ext i j
    have h1 := congrArg (fun w : LinearMap.range N.mulVecLin => (w : Fin 3 → K) i) (hφ j)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
    rw [vecMulVec_apply, mul_comm, h1]
    simp

theorem isRefl_of_rank_one {g : GL (Fin 3) K} (hsq : g * g = 1)
    (hrk : ((g : Matrix (Fin 3) (Fin 3) K) - 1).rank = 1) : IsRefl g := by
  obtain ⟨r, φ', hr, hN⟩ := exists_vecMulVec_of_rank_one hrk
  have hg : (g : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec r φ' := by
    rw [← hN]; abel
  have hsq' : (g : Matrix (Fin 3) (Fin 3) K) * g = 1 := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hsq
    simpa using this
  have hne : vecMulVec r φ' ≠ 0 := by
    intro h0
    rw [h0] at hN
    rw [hN] at hrk
    simp at hrk
  have key : (2 + φ' ⬝ᵥ r) • vecMulVec r φ' = 0 := by
    rw [hg] at hsq'
    have hNN : vecMulVec r φ' * vecMulVec r φ' = (φ' ⬝ᵥ r) • vecMulVec r φ' := by
      rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
    have h1 : (1 + vecMulVec r φ') * (1 + vecMulVec r φ') =
        1 + vecMulVec r φ' + vecMulVec r φ' + vecMulVec r φ' * vecMulVec r φ' := by noncomm_ring
    rw [h1, hNN] at hsq'
    have h3 : (1 : Matrix (Fin 3) (Fin 3) K) + vecMulVec r φ' + vecMulVec r φ' +
        (φ' ⬝ᵥ r) • vecMulVec r φ' = 1 + (2 + φ' ⬝ᵥ r) • vecMulVec r φ' := by
      rw [add_smul, two_smul]; abel
    rw [h3] at hsq'
    simpa using hsq'
  have hdot : φ' ⬝ᵥ r = -2 := by
    rcases smul_eq_zero.mp key with h | h
    · linear_combination h
    · exact absurd h hne
  refine ⟨r, -φ', hr, ?_, ?_⟩
  · rw [neg_dotProduct, hdot]; ring
  · rw [hg, vecMulVec_neg, sub_neg_eq_add]

end CFSG.RankThree.PartOne.N1322
