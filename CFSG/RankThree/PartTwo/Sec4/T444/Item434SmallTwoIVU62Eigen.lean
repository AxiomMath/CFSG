module

public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62

open Matrix Module

variable {K : Type*} [Field K]

theorem false_of_cube_scalar (h2 : (2 : K) = 0) (hK : ∀ x : K, x ≠ 0 → x ^ 3 = 1)
    {a b r : Matrix (Fin 6) (Fin 6) K} {c d : K} (ha3 : a ^ 3 = 1) (hb : IsUnit b)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hab : a * b = c • (b * a)) (hra : r * a = a * r)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1) (hr3 : r ^ 3 = d • 1) : False := by
  classical
  have hc3 : c ^ 3 = 1 := hK c hc0
  have hd3 : d ^ 3 = 1 := hK d hd0
  have hcc : 1 + c + c ^ 2 = 0 := by
    have h : (c - 1) * (1 + c + c ^ 2) = 0 := by linear_combination hc3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc1)
  have h3 : (3 : K) = 1 := by linear_combination h2
  set fa : Module.End K (Fin 6 → K) := Matrix.toLinAlgEquiv' a with hfa
  set fb : Module.End K (Fin 6 → K) := Matrix.toLinAlgEquiv' b with hfb
  set fr : Module.End K (Fin 6 → K) := Matrix.toLinAlgEquiv' r with hfr
  have hfa3 : fa ^ 3 = 1 := by rw [hfa, ← map_pow, ha3, map_one]
  have hfab : fa * fb = c • (fb * fa) := by
    have := congrArg Matrix.toLinAlgEquiv' hab
    simpa [map_mul, map_smul] using this
  have hfra : fr * fa = fa * fr := by rw [hfr, hfa, ← map_mul, ← map_mul, hra]
  have hfr3 : fr ^ 3 = d • (1 : Module.End K (Fin 6 → K)) := by
    have := congrArg Matrix.toLinAlgEquiv' hr3
    simpa [map_pow, map_smul, map_one] using this
  have hfbinj : Function.Injective fb := by
    have := (Matrix.mulVec_injective_iff_isUnit.mpr hb)
    exact this
  have hv3 : ∀ v, fa (fa (fa v)) = v := fun v => by
    have := congrArg (fun g : Module.End K (Fin 6 → K) => g v) hfa3
    simpa [pow_succ] using this
  let E : Fin 3 → Submodule K (Fin 6 → K) := fun i => Module.End.eigenspace fa (c ^ (i : ℕ))
  have hlam : Function.Injective (fun i : Fin 3 => c ^ (i : ℕ)) := by
    have h20 : c ^ 2 ≠ 1 := fun h => hc1 (by
      have : c = c ^ 3 / c ^ 2 := by field_simp
      rw [this, hc3, h, div_one])
    have h21 : c ^ 2 ≠ c := fun h => hc1 (by
      have : c * (c - 1) = 0 := by linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0))
    intro i j hij
    have hij' : c ^ (i : ℕ) = c ^ (j : ℕ) := hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (by simpa using hij') (Ne.symm hc1)
    · exact absurd (by simpa using hij'.symm) h20
    · exact absurd (by simpa using hij') hc1
    · rfl
    · exact absurd (by simpa using hij'.symm) h21
    · exact absurd (by simpa using hij') h20
    · exact absurd (by simpa using hij') h21
    · rfl
  have hind : iSupIndep E := (Module.End.eigenspaces_iSupIndep fa).comp hlam
  have hu0 : ∀ v, v + fa v + fa (fa v) ∈ E 0 := fun v => by
    simp only [E, Module.End.mem_eigenspace_iff]
    simp only [map_add, hv3, Fin.val_zero, pow_zero, one_smul]
    abel
  have hu1 : ∀ v, v + c ^ 2 • fa v + c • fa (fa v) ∈ E 1 := fun v => by
    simp only [E, Module.End.mem_eigenspace_iff]
    simp only [map_add, map_smul, hv3, Fin.val_one, pow_one]
    match_scalars <;> first | ring1 | linear_combination -hc3
  have hu2 : ∀ v, v + c • fa v + c ^ 2 • fa (fa v) ∈ E 2 := fun v => by
    simp only [E, Module.End.mem_eigenspace_iff]
    simp only [map_add, map_smul, hv3, Fin.val_two]
    match_scalars <;> first | ring1 | linear_combination -hc3 | linear_combination hc3 |
      linear_combination (-c) * hc3
  have hsum : ∀ v, v = (v + fa v + fa (fa v)) + (v + c ^ 2 • fa v + c • fa (fa v)) +
      (v + c • fa v + c ^ 2 • fa (fa v)) := fun v => by
    match_scalars <;> first | ring1 | linear_combination -h3 | linear_combination h3 |
      linear_combination hcc | linear_combination -hcc
  have htop : iSup E = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [hsum v]
    exact add_mem
      (add_mem (Submodule.mem_iSup_of_mem 0 (hu0 v)) (Submodule.mem_iSup_of_mem 1 (hu1 v)))
      (Submodule.mem_iSup_of_mem 2 (hu2 v))
  have hint : DirectSum.IsInternal E :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hfin : Module.finrank K (Fin 6 → K) = ∑ i : Fin 3, Module.finrank K (E i) := by
    have e : (DirectSum (Fin 3) fun i => E i) ≃ₗ[K] (Fin 6 → K) :=
      LinearEquiv.ofBijective (DirectSum.coeLinearMap E) hint
    rw [← e.finrank_eq, Module.finrank_directSum]
  rw [Module.finrank_fin_fun, Fin.sum_univ_three] at hfin
  have hb0 : ∀ v ∈ E 0, fb v ∈ E 1 := fun v hv => by
    simp only [E, Module.End.mem_eigenspace_iff, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      one_smul] at hv ⊢
    have := congrArg (fun g : Module.End K (Fin 6 → K) => g v) hfab
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hv]
  have hb1 : ∀ v ∈ E 1, fb v ∈ E 2 := fun v hv => by
    simp only [E, Module.End.mem_eigenspace_iff, Fin.val_one, Fin.val_two, pow_one] at hv ⊢
    have := congrArg (fun g : Module.End K (Fin 6 → K) => g v) hfab
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hv, map_smul, smul_smul, pow_two]
  have hb2 : ∀ v ∈ E 2, fb v ∈ E 0 := fun v hv => by
    simp only [E, Module.End.mem_eigenspace_iff, Fin.val_zero, Fin.val_two, pow_zero,
      one_smul] at hv ⊢
    have := congrArg (fun g : Module.End K (Fin 6 → K) => g v) hfab
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hv, map_smul, smul_smul, ← pow_succ', hc3, one_smul]
  have hn01 : Module.finrank K (E 0) ≤ Module.finrank K (E 1) :=
    LinearMap.finrank_le_finrank_of_injective (f := fb.restrict hb0)
      (fun x y hxy => Subtype.ext (hfbinj (congrArg Subtype.val hxy)))
  have hn12 : Module.finrank K (E 1) ≤ Module.finrank K (E 2) :=
    LinearMap.finrank_le_finrank_of_injective (f := fb.restrict hb1)
      (fun x y hxy => Subtype.ext (hfbinj (congrArg Subtype.val hxy)))
  have hn20 : Module.finrank K (E 2) ≤ Module.finrank K (E 0) :=
    LinearMap.finrank_le_finrank_of_injective (f := fb.restrict hb2)
      (fun x y hxy => Subtype.ext (hfbinj (congrArg Subtype.val hxy)))
  have hn0 : Module.finrank K (E 0) = 2 := by omega
  have hr0 : ∀ v ∈ E 0, fr v ∈ E 0 := fun v hv => by
    simp only [E, Module.End.mem_eigenspace_iff, Fin.val_zero, pow_zero, one_smul] at hv ⊢
    have := congrArg (fun g : Module.End K (Fin 6 → K) => g v) hfra
    simp only [Module.End.mul_apply] at this
    rw [← this, hv]
  set ρ : Module.End K (E 0) := fr.restrict hr0 with hρ
  have hρ3 : ρ ^ 3 = d • (1 : Module.End K (E 0)) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun g : Module.End K (Fin 6 → K) => g (x : Fin 6 → K)) hfr3
    simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, hρ, LinearMap.coe_restrict_apply, Submodule.coe_smul] at this ⊢
    exact this
  have hdet : (LinearMap.det ρ) ^ 3 = d ^ 2 := by
    have h1 := congrArg LinearMap.det hρ3
    rw [map_pow, LinearMap.det_smul, map_one, hn0, mul_one] at h1
    exact h1
  by_cases hdz : LinearMap.det ρ = 0
  · rw [hdz] at hdet
    have hd2 : d ^ 2 = 0 := by rw [← hdet]; ring
    exact hd0 ((pow_eq_zero_iff (by norm_num)).mp hd2)
  · rw [hK _ hdz] at hdet
    apply hd1
    calc d = d * d ^ 2 := by rw [← hdet, mul_one]
      _ = d ^ 3 := by ring
      _ = 1 := hd3

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
