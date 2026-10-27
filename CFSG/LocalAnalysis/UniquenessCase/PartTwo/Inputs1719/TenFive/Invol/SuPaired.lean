module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuEichler
import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_eichler_inv_paired (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K}
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = -1) (hAs : ∀ c : K, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c • 1) :
    ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * hypEichler h v w γ =
        hypEichler h v (-w) (h.bar γ) * A := by
  classical
  have htwo : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hne : ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) + l • 1) ≠ 0 := by
    intro h0
    refine hAs (-l) ?_
    rw [eq_neg_of_add_eq_zero_left h0, neg_smul]
  obtain ⟨y, hy⟩ : ∃ y : HypIndex r ε → K,
      ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) + l • 1) *ᵥ y ≠ 0 := by
    by_contra hc
    have hc' : ∀ y : HypIndex r ε → K,
        ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) + l • 1) *ᵥ y = 0 := by
      intro y
      by_contra h
      exact hc ⟨y, h⟩
    exact hne (Matrix.ext_of_mulVec_single (N := 0) fun j => by
      rw [hc' (Pi.single j 1), Matrix.zero_mulVec])
  set v : HypIndex r ε → K := ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) + l • 1) *ᵥ y
    with hv
  have hv0 : v ≠ 0 := by rw [hv]; exact hy
  have hAv : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v = l • v := by
    rw [hv, Matrix.mulVec_mulVec]
    have hmul : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) + l • 1) =
        l • ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) + l • 1) := by
      rw [Matrix.mul_add, hAA, Matrix.mul_smul, Matrix.mul_one, smul_add,
        smul_smul, pow_two, add_comm]
    rw [hmul, Matrix.smul_mulVec]
  have hiso : ∀ x y : HypIndex r ε → K,
      hypForm h r ε ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x)
        ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) = hypForm h r ε x y :=
    (gramForm_isometry_iff h (hypGram r ε K)
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K)).mpr (mem_hypUnitary.mp hA)
  have hvv0 : hypForm h r ε v v = 0 := by
    have h1 : hypForm h r ε (l • v) (l • v) = hypForm h r ε v v := by
      rw [← hAv]
      exact hiso v v
    have h2 : hypForm h r ε (l • v) (l • v) = h.norm l * hypForm h r ε v v := by
      rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul,
        UnitaryFieldData.norm]
      ring
    have h3 : hypForm h r ε v v = -hypForm h r ε v v := by
      calc hypForm h r ε v v = hypForm h r ε (l • v) (l • v) := h1.symm
        _ = h.norm l * hypForm h r ε v v := h2
        _ = -hypForm h r ε v v := by rw [hN, neg_one_mul]
    have h4 : (2 : K) * hypForm h r ε v v = 0 := by
      have h5 := congrArg (fun t : K => t + hypForm h r ε v v) h3
      simpa [two_mul] using h5
    exact (mul_eq_zero.mp h4).resolve_left htwo
  obtain ⟨θ, hθ0, hθbar⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow.exists_bar_eq_neg h
  refine ⟨v, 0, θ, ⟨hv0, hvv0, by simp, by simp [hθbar], Or.inr ⟨rfl, hθ0⟩⟩, ?_⟩
  have hE := mul_hypEichler_of_mem_hypUnitary h hA v (0 : HypIndex r ε → K) θ
  rw [hAv, Matrix.mulVec_zero] at hE
  have hE' : hypEichler h (l • v) (0 : HypIndex r ε → K) θ =
      hypEichler h v 0 (h.bar θ) := by
    rw [hypEichler_smul_left, smul_zero, hN, neg_one_mul, hθbar]
  rw [hE'] at hE
  simpa using hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
