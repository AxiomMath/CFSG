module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuEichler
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private lemma exists_mulVec_ne_zero {M : Matrix (HypIndex r ε) (HypIndex r ε) K} (hM : M ≠ 0) :
    ∃ y : HypIndex r ε → K, M *ᵥ y ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [h (Pi.single j 1), Matrix.zero_mulVec]

theorem exists_eichler_inv_split (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K}
    (hl0 : l ≠ 0) (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = 1) (hAs : ∀ c : K, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c • 1) :
    ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * hypEichler h v w γ =
        hypEichler h v (-w) (h.bar γ) * A := by
  classical
  obtain ⟨d, hd, v₁, v₂, hAv₁, hAv₂, h11, h22, h12⟩ :=
    OddUnitaryInvolutionSylow.exists_orthonormal_eigen_pair h hp2 hn hA hl0 hAA hN
  obtain ⟨c, hcN⟩ := OddUnitaryInvolutionSylow.exists_norm_eq_neg_one h
  have hcN' : c * h.bar c = -1 := hcN
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hB : (hypForm h r ε).IsSymm := hypForm_isSymm h
  have h21 : hypForm h r ε v₂ v₁ = 0 := by rw [← hB.eq v₁ v₂, h12, map_zero]
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp [UnitaryFieldData.norm] at hd
  have hcoef : h.bar d * (-d) = -1 := by
    have hcomm : h.bar d * d = 1 := (mul_comm (h.bar d) d).trans hd
    rw [mul_neg, hcomm]
  set v : HypIndex r ε → K := v₁ + c • v₂ with hv
  have hvv : hypForm h r ε v v = 0 := by
    simp only [hv, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
      h11, h22, h12, h21]
    linear_combination hcN'
  have hv1 : hypForm h r ε v₁ v = 1 := by
    simp only [hv, map_add, map_smul, smul_eq_mul,
      h11, h12]
    ring
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hv1
    simp at hv1
  have hAv : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v = d • v := by
    rw [hv, mulVec_add, mulVec_smul, hAv₁, hAv₂, smul_add, smul_comm c d]
  have hd2 : d ^ 2 = l ^ 2 := by
    have hmv : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v₁) = (l ^ 2) • v₁ := by
      rw [Matrix.mulVec_mulVec, hAA, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hmv2 : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v₁) = (d * d) • v₁ := by
      rw [hAv₁, Matrix.mulVec_smul, hAv₁, smul_smul]
    have hv1ne : v₁ ≠ 0 := by
      intro h0
      rw [h0] at h11
      simp at h11
    have hk : d * d - l ^ 2 = 0 := by
      have h0 : (d * d - l ^ 2) • v₁ = 0 := by rw [sub_smul, ← hmv2, hmv, sub_self]
      exact (smul_eq_zero.mp h0).resolve_right hv1ne
    rw [pow_two]
    exact sub_eq_zero.mp hk
  have hfac : ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) + d • 1) *
      ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) - d • 1) = 0 := by
    simp only [add_mul, mul_sub, hAA, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul]
    rw [show d * d = d ^ 2 by ring, hd2]
    module
  have hne : ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) - d • 1) ≠ 0 := by
    intro h0
    exact hAs d (sub_eq_zero.mp h0)
  obtain ⟨y, hy⟩ := exists_mulVec_ne_zero hne
  set w : HypIndex r ε → K :=
    ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) - d • 1) *ᵥ y with hw
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact hy
  have hAw : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w = (-d) • w := by
    have hkey : ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) + d • 1) *ᵥ w = 0 := by
      rw [hw, Matrix.mulVec_mulVec, hfac, Matrix.zero_mulVec]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hkey
    exact (eq_neg_of_add_eq_zero_left hkey).trans (neg_smul d w).symm
  have hiso : ∀ x y, hypForm h r ε ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x)
      ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) = hypForm h r ε x y := by
    intro x y
    have h := gramForm_mulVec h (hypGram r ε K)
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) x y
    rw [mem_hypUnitary.mp hA] at h
    exact h
  have hvw : hypForm h r ε v w = 0 := by
    have hcoe : hypForm h r ε (d • v) ((-d) • w) =
        (h.bar d * (-d)) * hypForm h r ε v w := by
      have h1 : hypForm h r ε (d • v) = h.bar d • hypForm h r ε v :=
        LinearMap.map_smulₛₗ (f := hypForm h r ε) d v
      rw [h1, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    have hfin : hypForm h r ε v w = -hypForm h r ε v w := by
      calc hypForm h r ε v w
          = hypForm h r ε ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v)
              ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w) := (hiso v w).symm
        _ = hypForm h r ε (d • v) ((-d) • w) := by rw [hAv, hAw]
        _ = (h.bar d * (-d)) * hypForm h r ε v w := hcoe
        _ = -hypForm h r ε v w := by rw [hcoef, neg_one_mul]
    have hzero : hypForm h r ε v w + hypForm h r ε v w = 0 := by
      have := congrArg (fun x => x + hypForm h r ε v w) hfin
      simpa using this
    have h2h : (2 : K) * hypForm h r ε v w = 0 := by
      rw [two_mul]
      exact hzero
    exact (mul_eq_zero.mp h2h).resolve_left h2
  set γ : K := -(hypForm h r ε w w) * (2 : K)⁻¹ with hγ
  have hbar_ww : h.bar (hypForm h r ε w w) = hypForm h r ε w w := hB.eq w w
  have hγbar : h.bar γ = γ := by
    rw [hγ, map_mul, map_neg, map_inv₀, hbar_ww, map_ofNat]
  have hγtrace : γ + h.bar γ + hypForm h r ε w w = 0 := by
    have h2inv : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
    rw [hγbar, hγ]
    linear_combination (-(hypForm h r ε w w)) * h2inv
  have hwspan : w ∉ Submodule.span K ({v} : Set (HypIndex r ε → K)) := by
    intro hmem
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w = d • w := by
      rw [← hμ, Matrix.mulVec_smul, hAv, smul_smul, smul_smul, mul_comm]
    have heq : (-d) • w = d • w := by rw [← hAw, h1]
    have hzero : ((-d) - d) • w = 0 := by rw [sub_smul, heq, sub_self]
    have hcoef' : (-d) - d = 0 := (smul_eq_zero.mp hzero).resolve_right hw0
    have h2d : (2 : K) * d = 0 := by linear_combination -hcoef'
    exact hd0 ((mul_eq_zero.mp h2d).resolve_left h2)
  refine ⟨v, w, γ, ⟨hv0, hvv, hvw, hγtrace, Or.inl hwspan⟩, ?_⟩
  have hbarw : h.bar d • ((-d) • w) = -w := by
    rw [smul_smul, hcoef, neg_one_smul]
  rw [mul_hypEichler_of_mem_hypUnitary h hA v w γ, hAv, hAw,
    hypEichler_smul_left h d v ((-d) • w) γ, hbarw, hd, one_mul, hγbar]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
