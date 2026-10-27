module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriOctId
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.Open Module

section General

variable {K : Type*} [Field K]

theorem finrank_oct_eq_eight : finrank K (Oct K) = 8 := by
  simp [Oct]

theorem exists_octPolar_eq_one {y : Oct K} (hy : y ≠ 0) : ∃ z : Oct K, octPolar y z = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  rcases j with j | j
  · induction j using Fin.cases with
    | zero =>
      refine ⟨Pi.single (.inr 0) (y (.inl 0))⁻¹, ?_⟩
      simp [octPolar_eq, octA, octB, octU, octW, dot3, Pi.single_apply] at hj ⊢
      exact mul_inv_cancel₀ hj
    | succ i =>
      refine ⟨Pi.single (.inr i.succ) (-(y (.inl i.succ))⁻¹), ?_⟩
      fin_cases i <;> simp [octPolar_eq, octA, octB, octU, octW, dot3, Pi.single_apply] at hj ⊢ <;>
        exact mul_inv_cancel₀ hj
  · induction j using Fin.cases with
    | zero =>
      refine ⟨Pi.single (.inl 0) (y (.inr 0))⁻¹, ?_⟩
      simp [octPolar_eq, octA, octB, octU, octW, dot3, Pi.single_apply] at hj ⊢
      exact inv_mul_cancel₀ hj
    | succ i =>
      refine ⟨Pi.single (.inl i.succ) (-(y (.inr i.succ))⁻¹), ?_⟩
      fin_cases i <;> simp [octPolar_eq, octA, octB, octU, octW, dot3, Pi.single_apply] at hj ⊢ <;>
        exact inv_mul_cancel₀ hj

theorem octPolarBil_nondegenerate : (octPolarBil (K := K)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · by_contra hx0
    obtain ⟨z, hz⟩ := exists_octPolar_eq_one hx0
    have h := hx z
    rw [octPolarBil_apply, hz] at h
    exact one_ne_zero h
  · by_contra hy0
    obtain ⟨z, hz⟩ := exists_octPolar_eq_one hy0
    have h := hy z
    rw [octPolarBil_apply, octPolar_comm, hz] at h
    exact one_ne_zero h

theorem finrank_le_four_of_octNorm_eq_zero (W : Submodule K (Oct K))
    (hW : ∀ v ∈ W, octNorm v = 0) : finrank K W ≤ 4 := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal octPolarBil W := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [octPolarBil_apply, octPolar, hW _ (W.add_mem hn hv), hW _ hn, hW _ hv]
    ring
  have h := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal octPolarBil_nondegenerate W,
    finrank_oct_eq_eight] at h
  omega

private theorem finrank_range_eq_four_of_ker_eq_range {f g : Oct K →ₗ[K] Oct K}
    (hf : ∀ v ∈ LinearMap.range f, octNorm v = 0) (hg : ∀ v ∈ LinearMap.range g, octNorm v = 0)
    (hfg : LinearMap.ker f = LinearMap.range g) : finrank K (LinearMap.range f) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hfg, finrank_oct_eq_eight] at h
  have h1 := finrank_le_four_of_octNorm_eq_zero _ hf
  have h2 := finrank_le_four_of_octNorm_eq_zero _ hg
  omega

private theorem octConj_ne_zero {y : Oct K} (hy : y ≠ 0) : octConj y ≠ 0 := by
  intro h
  apply hy
  have h0 : octConj (0 : Oct K) = 0 :=
    oct_ext (by simp) (funext fun i => by simp) (funext fun i => by simp) (by simp)
  rw [← octConj_conj y, h, h0]

theorem range_mulRight_eq_top_of_norm_ne_zero {y : Oct K} (hy : octNorm y ≠ 0) :
    LinearMap.range (octMulBil.flip y) = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun v => ⟨(octNorm y)⁻¹ • octMul v (octConj y), ?_⟩
  simp [octMul_smul_left, octMul_mul_conj_right, hy]

theorem finrank_range_mulRight_of_norm_ne_zero {y : Oct K} (hy : octNorm y ≠ 0) :
    finrank K (LinearMap.range (octMulBil.flip y)) = 8 := by
  rw [range_mulRight_eq_top_of_norm_ne_zero hy, finrank_top, finrank_oct_eq_eight]

theorem range_mulRight_le_ker_mulRight_conj {y : Oct K} (hy : octNorm y = 0) :
    LinearMap.range (octMulBil.flip y) ≤ LinearMap.ker (octMulBil.flip (octConj y)) := by
  rintro _ ⟨x, rfl⟩
  simp [octMul_mul_conj, hy]

theorem ker_mulRight_le_range_mulRight_conj {y : Oct K} (hy : y ≠ 0) :
    LinearMap.ker (octMulBil.flip y) ≤ LinearMap.range (octMulBil.flip (octConj y)) := by
  intro x hx
  obtain ⟨z, hz⟩ := exists_octPolar_eq_one hy
  have hxy : octMul x y = 0 := hx
  have h := octMul_mul_conj_lin y z x
  rw [hxy, octMul_zero_left, zero_add, hz, one_smul] at h
  exact ⟨octMul x z, h⟩

theorem ker_mulRight_eq_range_mulRight_conj {y : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0) :
    LinearMap.ker (octMulBil.flip y) = LinearMap.range (octMulBil.flip (octConj y)) := by
  refine le_antisymm (ker_mulRight_le_range_mulRight_conj hy0) ?_
  have h := range_mulRight_le_ker_mulRight_conj (y := octConj y) (by rwa [octNorm_conj])
  rwa [octConj_conj] at h

theorem range_mulRight_eq_ker_mulRight_conj {y : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0) :
    LinearMap.range (octMulBil.flip y) = LinearMap.ker (octMulBil.flip (octConj y)) := by
  refine le_antisymm (range_mulRight_le_ker_mulRight_conj hy) ?_
  have h := ker_mulRight_le_range_mulRight_conj (y := octConj y) (octConj_ne_zero hy0)
  rwa [octConj_conj] at h

theorem octNorm_eq_zero_of_mem_range_mulRight {y v : Oct K} (hy : octNorm y = 0)
    (hv : v ∈ LinearMap.range (octMulBil.flip y)) : octNorm v = 0 := by
  obtain ⟨x, rfl⟩ := hv
  rw [LinearMap.flip_apply, octMulBil_apply, octNorm_mul, hy, mul_zero]

theorem octNorm_eq_zero_of_mem_ker_mulRight {y v : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0)
    (hv : v ∈ LinearMap.ker (octMulBil.flip y)) : octNorm v = 0 := by
  rw [ker_mulRight_eq_range_mulRight_conj hy0 hy] at hv
  exact octNorm_eq_zero_of_mem_range_mulRight (by rwa [octNorm_conj]) hv

theorem finrank_range_mulRight_of_singular {y : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0) :
    finrank K (LinearMap.range (octMulBil.flip y)) = 4 :=
  finrank_range_eq_four_of_ker_eq_range
    (fun _ hv => octNorm_eq_zero_of_mem_range_mulRight hy hv)
    (fun _ hv => octNorm_eq_zero_of_mem_range_mulRight (by rwa [octNorm_conj]) hv)
    (ker_mulRight_eq_range_mulRight_conj hy0 hy)

theorem finrank_ker_mulRight_of_singular {y : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0) :
    finrank K (LinearMap.ker (octMulBil.flip y)) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (octMulBil.flip y)
  rw [finrank_range_mulRight_of_singular hy0 hy, finrank_oct_eq_eight] at h
  omega

theorem range_mulLeft_eq_top_of_norm_ne_zero {x : Oct K} (hx : octNorm x ≠ 0) :
    LinearMap.range (octMulBil x) = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun v => ⟨(octNorm x)⁻¹ • octMul (octConj x) v, ?_⟩
  simp [octMul_smul_right, octMul_mul_conj_left, hx]

theorem finrank_range_mulLeft_of_norm_ne_zero {x : Oct K} (hx : octNorm x ≠ 0) :
    finrank K (LinearMap.range (octMulBil x)) = 8 := by
  rw [range_mulLeft_eq_top_of_norm_ne_zero hx, finrank_top, finrank_oct_eq_eight]

theorem range_mulLeft_le_ker_mulLeft_conj {x : Oct K} (hx : octNorm x = 0) :
    LinearMap.range (octMulBil x) ≤ LinearMap.ker (octMulBil (octConj x)) := by
  rintro _ ⟨y, rfl⟩
  simp [octMul_conj_mul, hx]

theorem ker_mulLeft_le_range_mulLeft_conj {x : Oct K} (hx : x ≠ 0) :
    LinearMap.ker (octMulBil x) ≤ LinearMap.range (octMulBil (octConj x)) := by
  intro y hy
  obtain ⟨z, hz⟩ := exists_octPolar_eq_one hx
  have hxy : octMul x y = 0 := hy
  have h := octMul_conj_mul_lin x z y
  rw [hxy, octMul_zero_right, add_zero, hz, one_smul] at h
  exact ⟨octMul z y, h⟩

theorem ker_mulLeft_eq_range_mulLeft_conj {x : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0) :
    LinearMap.ker (octMulBil x) = LinearMap.range (octMulBil (octConj x)) := by
  refine le_antisymm (ker_mulLeft_le_range_mulLeft_conj hx0) ?_
  have h := range_mulLeft_le_ker_mulLeft_conj (x := octConj x) (by rwa [octNorm_conj])
  rwa [octConj_conj] at h

theorem range_mulLeft_eq_ker_mulLeft_conj {x : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0) :
    LinearMap.range (octMulBil x) = LinearMap.ker (octMulBil (octConj x)) := by
  refine le_antisymm (range_mulLeft_le_ker_mulLeft_conj hx) ?_
  have h := ker_mulLeft_le_range_mulLeft_conj (x := octConj x) (octConj_ne_zero hx0)
  rwa [octConj_conj] at h

theorem octNorm_eq_zero_of_mem_range_mulLeft {x v : Oct K} (hx : octNorm x = 0)
    (hv : v ∈ LinearMap.range (octMulBil x)) : octNorm v = 0 := by
  obtain ⟨y, rfl⟩ := hv
  rw [octMulBil_apply, octNorm_mul, hx, zero_mul]

theorem octNorm_eq_zero_of_mem_ker_mulLeft {x v : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0)
    (hv : v ∈ LinearMap.ker (octMulBil x)) : octNorm v = 0 := by
  rw [ker_mulLeft_eq_range_mulLeft_conj hx0 hx] at hv
  exact octNorm_eq_zero_of_mem_range_mulLeft (by rwa [octNorm_conj]) hv

theorem finrank_range_mulLeft_of_singular {x : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0) :
    finrank K (LinearMap.range (octMulBil x)) = 4 :=
  finrank_range_eq_four_of_ker_eq_range
    (fun _ hv => octNorm_eq_zero_of_mem_range_mulLeft hx hv)
    (fun _ hv => octNorm_eq_zero_of_mem_range_mulLeft (by rwa [octNorm_conj]) hv)
    (ker_mulLeft_eq_range_mulLeft_conj hx0 hx)

theorem finrank_ker_mulLeft_of_singular {x : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0) :
    finrank K (LinearMap.ker (octMulBil x)) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (octMulBil x)
  rw [finrank_range_mulLeft_of_singular hx0 hx, finrank_oct_eq_eight] at h
  omega

end General

end CFSG.RankThree.GF2n.Stroth80.Tri

end
