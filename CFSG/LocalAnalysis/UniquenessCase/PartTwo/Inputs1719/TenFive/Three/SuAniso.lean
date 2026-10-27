module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOrthogonality

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem exists_orth_notMem_span (h : UnitaryFieldData p f K) (hn : 4 ≤ 2 * r + ε)
    {v w : HypIndex r ε → K} (hv0 : v ≠ 0) :
    ∃ z, hypForm h r ε v z = 0 ∧ hypForm h r ε w z = 0 ∧ z ∉ Submodule.span K {v} := by
  classical
  set L : (HypIndex r ε → K) →ₗ[K] K × K :=
    LinearMap.prod (hypForm h r ε v) (hypForm h r ε w) with hL
  have hdim : Module.finrank K (HypIndex r ε → K) = 2 * r + ε := finrank_hypIndex_fun
  have hfr : 2 * r + ε - 2 ≤ Module.finrank K (LinearMap.ker L) := by
    have hsum := LinearMap.finrank_range_add_finrank_ker L
    have hle : Module.finrank K (LinearMap.range L) ≤ 2 := by
      have h1 := Submodule.finrank_le (LinearMap.range L)
      rw [Module.finrank_prod, Module.finrank_self] at h1
      omega
    omega
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : LinearMap.ker L ≤ Submodule.span K {v} := by
    intro y hy
    rw [hL, LinearMap.ker_prod, Submodule.mem_inf] at hy
    exact hcon y (LinearMap.mem_ker.mp hy.1) (LinearMap.mem_ker.mp hy.2)
  have h2 : 2 * r + ε - 2 ≤ Module.finrank K (Submodule.span K {v}) :=
    hfr.trans (Submodule.finrank_mono hle)
  rw [finrank_span_singleton hv0] at h2
  omega

private theorem notMem_span_pair (h : UnitaryFieldData p f K) {v w z : HypIndex r ε → K}
    (hvw : hypForm h r ε v w = 0) (hww : hypForm h r ε w w ≠ 0)
    (hzw : hypForm h r ε w z = 0) (hz : z ∉ Submodule.span K {v}) :
    z ∉ Submodule.span K ({v, w} : Set (HypIndex r ε → K)) := by
  intro hmem
  apply hz
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hwv : hypForm h r ε w v = 0 := by
    rw [← (hypForm_isSymm h).eq v w, hvw, map_zero]
  have hb : b = 0 := by
    have h1 : hypForm h r ε w z = a * hypForm h r ε w v + b * hypForm h r ε w w := by
      rw [← hab, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hzw, hwv, mul_zero, zero_add] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right hww
  rw [hb, zero_smul, add_zero] at hab
  rw [← hab]
  exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton v))

private theorem exists_orth_separating (h : UnitaryFieldData p f K) {v w z : HypIndex r ε → K}
    (hvw : hypForm h r ε v w = 0) (hww : hypForm h r ε w w ≠ 0) (hzw : hypForm h r ε w z = 0)
    (hz : z ∉ Submodule.span K {v}) :
    ∃ z', hypForm h r ε v z' = 0 ∧ hypForm h r ε w z' = 0 ∧ hypForm h r ε z z' ≠ 0 := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : LinearMap.ker (hypForm h r ε v) ⊓ LinearMap.ker (hypForm h r ε w) ≤
      LinearMap.ker (hypForm h r ε z) := by
    intro y hy
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hy
    exact LinearMap.mem_ker.mpr (hcon y hy.1 hy.2)
  have hinf : (⨅ i : Fin 2, LinearMap.ker (![hypForm h r ε v, hypForm h r ε w] i)) =
      LinearMap.ker (hypForm h r ε v) ⊓ LinearMap.ker (hypForm h r ε w) := by
    refine le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1)) (le_iInf fun i => ?_)
    fin_cases i <;> simp
  have hspan := mem_span_of_iInf_ker_le_ker (𝕜 := K) (E := HypIndex r ε → K) (ι := Fin 2)
    (L := ![hypForm h r ε v, hypForm h r ε w]) (K := hypForm h r ε z) (by rw [hinf]; exact hle)
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hspan
  obtain ⟨a, b, hab⟩ := hspan
  have hzero : hypForm h r ε (z - h.bar a • v - h.bar b • w) = 0 := by
    rw [map_sub, map_sub, map_smulₛₗ, map_smulₛₗ, UnitaryFieldData.bar_bar,
      UnitaryFieldData.bar_bar, ← hab]
    abel
  have hz0 : z - h.bar a • v - h.bar b • w = 0 := by
    refine hypForm_separatingLeft h _ fun y => ?_
    rw [hzero]
    simp
  have h1 : z = h.bar a • v + h.bar b • w := by
    rw [← sub_eq_zero]
    have he : z - (h.bar a • v + h.bar b • w) = z - h.bar a • v - h.bar b • w := by abel
    rw [he, hz0]
  apply notMem_span_pair h hvw hww hzw hz
  rw [h1]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert v {w})))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem v rfl)))

theorem exists_aniso_orth (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hn : 4 ≤ 2 * r + ε)
    {v w : HypIndex r ε → K} (hv0 : v ≠ 0) (hvw : hypForm h r ε v w = 0)
    (hw : hypForm h r ε w w ≠ 0) :
    ∃ y : HypIndex r ε → K, hypForm h r ε v y = 0 ∧ hypForm h r ε w y = 0 ∧
      hypForm h r ε y y ≠ 0 := by
  classical
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two hp2
  obtain ⟨z, hzv, hzw, hz⟩ := exists_orth_notMem_span h hn hv0 (w := w)
  obtain ⟨z', hz'v, hz'w, hzz'⟩ := exists_orth_separating h hvw hw hzw hz
  set c : K := (hypForm h r ε z z')⁻¹ with hc
  have hcz : hypForm h r ε z (c • z') = 1 := by
    rw [map_smul, smul_eq_mul, hc, inv_mul_cancel₀ hzz']
  have hzv' : hypForm h r ε v (c • z') = 0 := by rw [map_smul, hz'v, smul_zero]
  have hzw' : hypForm h r ε w (c • z') = 0 := by rw [map_smul, hz'w, smul_zero]
  have hcz' : hypForm h r ε (c • z') z = 1 := by
    rw [← (hypForm_isSymm h).eq z (c • z'), hcz, map_one]
  by_cases hzz : hypForm h r ε z z = 0
  · by_cases hz'z' : hypForm h r ε (c • z') (c • z') = 0
    · refine ⟨z + c • z', ?_, ?_, ?_⟩
      · rw [map_add, hzv, hzv', add_zero]
      · rw [map_add, hzw, hzw', add_zero]
      · have hsum : hypForm h r ε (z + c • z') (z + c • z') = 2 := by
          simp only [map_add, LinearMap.add_apply, hzz, hcz, hcz', hz'z']
          norm_num
        rw [hsum]
        exact h2
    · exact ⟨c • z', hzv', hzw', hz'z'⟩
  · exact ⟨z, hzv, hzw, hzz⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
