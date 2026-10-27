module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeCompEq
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeComp
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeQS
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeNe
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeEigen
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeCQ
import CFSG.RankThree.PartTwo.Sec21.Hering214KEig

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section Helpers

open Matrix CFSG.LocalAnalysis.ComponentInitial

private lemma uniCubeBlock_cube_root_pow_three {K : Type} [Field K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h
  exact sub_eq_zero.mp h.symm

private lemma uniCubeBlock_cube_root_eq_one_or_sq {K : Type} [Field K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    ∀ μ : K, μ ^ 3 = 1 → μ = 1 ∨ μ = ω ∨ μ = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := uniCubeBlock_cube_root_pow_three hω
  have hsum : ω + ω ^ 2 = -1 := by
    calc ω + ω ^ 2 = (ω ^ 2 + ω + 1) - 1 := by ring
      _ = -1 := by rw [hω, zero_sub]
  have hprod : ω * ω ^ 2 = 1 := by
    rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω3]
  intro μ hμ
  have hfac : (μ - 1) * (μ ^ 2 + μ + 1) = 0 := by
    calc (μ - 1) * (μ ^ 2 + μ + 1) = μ ^ 3 - 1 := by ring
      _ = 0 := by rw [hμ]; ring
  rcases mul_eq_zero.mp hfac with h1 | hq
  · left; exact sub_eq_zero.mp h1
  · right
    have hquad : (μ - ω) * (μ - ω ^ 2) = 0 := by
      calc (μ - ω) * (μ - ω ^ 2) = μ ^ 2 - (ω + ω ^ 2) * μ + ω * ω ^ 2 := by ring
        _ = μ ^ 2 + μ + 1 := by rw [hsum, hprod]; ring
        _ = 0 := hq
    rcases mul_eq_zero.mp hquad with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)

private lemma uniCubeBlock_one_ne_omega_sq {K : Type} [Field K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : (1 : K) ≠ ω ^ 2 := by
  intro h
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : (1 : K) + ω + 1 = 0 := by simpa [← h] using hω
  have h2 : ω + 2 = 0 := by
    rw [show (1 : K) + ω + 1 = ω + 2 by ring] at h1
    exact h1
  rw [htwo, add_zero] at h2
  rw [h2] at hω
  have h10 : (1 : K) = 0 := by simpa using hω
  exact one_ne_zero h10

private lemma uniCubeBlock_omega_ne_sq {K : Type} [Field K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ ω ^ 2 := by
  intro h
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsum : ω + ω + 1 = 0 := by
    have h' := hω
    rw [← h] at h'
    exact h'
  have h2 : (2 : K) * ω + 1 = 0 := by
    have : (2 : K) * ω + 1 = ω + ω + 1 := by ring
    rw [this]; exact hsum
  rw [htwo, zero_mul, zero_add] at h2
  exact one_ne_zero h2

private theorem uniCubeBlock_no_second_block {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hN : 4 ≤ N)
    {d : GL (Fin N) K} (hd : IsHermIsometry q (d : Matrix (Fin N) (Fin N) K)) (hd3 : d ^ 3 = 1)
    {δ' : MulAut (PSUg N K q)} (hδ : IsConjBy d δ') {J' : Subgroup (PSUg N K q)}
    (huniq : ∀ Q : Subgroup (PSUg N K q), IsComponentOf Q (ggAutFixedSubgroup δ') → Q = J')
    {μ : K} (hμ3 : μ ^ 3 = 1) (hJμ : ∀ x, x ∈ J' ↔ InCubeBlock d μ x)
    (hμ2 : 2 ≤ Module.finrank K (cubeEigen d μ))
    {ν : K} (hν3 : ν ^ 3 = 1) (hνne : ν ≠ μ)
    (hν2 : 2 ≤ Module.finrank K (cubeEigen d ν)) (hq4 : 4 ≤ q) : False := by
  have hνQS : CubeBlockQS q d ν := Or.inl ⟨hν2, hq4⟩
  obtain ⟨Qν, hQνc, hQνmem, -⟩ :=
    uni_cube_block_component hK hq3 hN hd hd3 hδ hν3 hνQS
  have hQνJ : Qν = J' := huniq Qν hQνc
  exact (uni_cube_blocks_ne hK hq3 hN hd hd3 hμ3 hν3 hνne.symm hμ2 hν2)
    (fun x => by rw [← hJμ x, ← hQνJ, hQνmem x])

private theorem uniCubeBlock_isHermIsometry_of_mem_largeEvenSU {K : Type} [Field K] [Finite K] [CharP K 2]
    {f N : ℕ} (h : UnitaryFieldData 2 f K) {g : GL (Fin N) K}
    (hg : g ∈ LargeEvenSUGroup (Fin N) K (2 ^ f)) :
    IsHermIsometry (2 ^ f) (g : Matrix (Fin N) (Fin N) K) := by
  have hiso := ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h).mp
    (show g ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K N from hg)).2
  intro v w
  have h1 := hiso v w
  rw [CFSG.LinearGroups.stdHermForm_apply, CFSG.LinearGroups.stdHermForm_apply] at h1
  simpa only [UnitaryFieldData.bar_apply] using h1

private lemma uniCubeBlock_add_pow_two_pow {K : Type} [Field K] [CharP K 2] (f : ℕ) (a b : K) :
    (a + b) ^ (2 ^ f) = a ^ (2 ^ f) + b ^ (2 ^ f) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact add_pow_char_pow a b 2 f

private lemma uniCubeBlock_sum_pow_add {K : Type} [Field K] [CharP K 2] {N : ℕ} (f : ℕ)
    (a b w : Fin N → K) :
    (∑ i, (a i + b i) ^ (2 ^ f) * w i) =
      (∑ i, a i ^ (2 ^ f) * w i) + ∑ i, b i ^ (2 ^ f) * w i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [uniCubeBlock_add_pow_two_pow f, add_mul]

private lemma uniCubeBlock_sum_mul_add {K : Type} [Field K] {N : ℕ} (q : ℕ) (v a b : Fin N → K) :
    (∑ i, v i ^ q * (a i + b i)) =
      (∑ i, v i ^ q * a i) + ∑ i, v i ^ q * b i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_add]

private lemma uniCubeBlock_sum_mul_single {K : Type} [Field K] {N : ℕ} (q : ℕ) (v : Fin N → K) (j : Fin N) :
    (∑ i, v i ^ q * (Pi.single j (1 : K) : Fin N → K) i) = v j ^ q := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma uniCubeBlock_eq_zero_of_sum_mul_eq_zero {K : Type} [Field K] {N : ℕ} (q : ℕ) (hq : q ≠ 0)
    {y : Fin N → K} (hy : ∀ z : Fin N → K, ∑ i, y i ^ q * z i = 0) : y = 0 := by
  funext j
  have h := hy (Pi.single j (1 : K))
  rw [uniCubeBlock_sum_mul_single q y j] at h
  exact (pow_eq_zero_iff hq).mp h

private lemma uniCubeBlock_mulVec_mem_cubeEigen_of_fixed {K : Type} [Field K] [Finite K] [CharP K 2]
    {N f : ℕ} (h : UnitaryFieldData 2 f K)
    {d : GL (Fin N) K} {μ : K} {W : Submodule K (Fin N → K)}
    (hV : cubeEigen d μ ⊔ W = ⊤)
    (horth₁ : ∀ a ∈ cubeEigen d μ, ∀ b ∈ W, ∑ i, a i ^ (2 ^ f) * b i = 0)
    (horth₂ : ∀ b ∈ W, ∀ a ∈ cubeEigen d μ, ∑ i, b i ^ (2 ^ f) * a i = 0)
    {g : GL (Fin N) K} (hg : g ∈ LargeEvenSUGroup (Fin N) K (2 ^ f))
    (hfix : ∀ w ∈ W, (g : Matrix (Fin N) (Fin N) K) *ᵥ w = w)
    {v : Fin N → K} (hv : v ∈ cubeEigen d μ) :
    (g : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ cubeEigen d μ := by
  have hiso := uniCubeBlock_isHermIsometry_of_mem_largeEvenSU h hg
  have hgv : (g : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ cubeEigen d μ ⊔ W := by
    rw [hV]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hgv
  have hxx : x + x = 0 := by
    have hk : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [← two_smul K x, hk, zero_smul]
  have hy_eq : y = (g : Matrix (Fin N) (Fin N) K) *ᵥ v + x := by
    have h1 : y = ((g : Matrix (Fin N) (Fin N) K) *ᵥ v) - x := by
      rw [← hxy]; abel
    have hneg : -x = x := by
      rw [neg_eq_iff_add_eq_zero]
      exact hxx
    rw [h1, sub_eq_add_neg, hneg]
  have hyz₂ : ∀ z₂ ∈ W, ∑ i, y i ^ (2 ^ f) * z₂ i = 0 := by
    intro z₂ hz₂
    have hgz₂ : (g : Matrix (Fin N) (Fin N) K) *ᵥ z₂ = z₂ := hfix z₂ hz₂
    calc ∑ i, y i ^ (2 ^ f) * z₂ i
        = ∑ i, ((g : Matrix (Fin N) (Fin N) K) *ᵥ v + x) i ^ (2 ^ f) * z₂ i := by rw [hy_eq]
      _ = ∑ i, (((g : Matrix (Fin N) (Fin N) K) *ᵥ v) i + x i) ^ (2 ^ f) * z₂ i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Pi.add_apply]
      _ = (∑ i, ((g : Matrix (Fin N) (Fin N) K) *ᵥ v) i ^ (2 ^ f) * z₂ i) +
            ∑ i, x i ^ (2 ^ f) * z₂ i := uniCubeBlock_sum_pow_add f _ _ _
      _ = (∑ i, ((g : Matrix (Fin N) (Fin N) K) *ᵥ v) i ^ (2 ^ f) * z₂ i) + 0 := by
            rw [horth₁ x hx z₂ hz₂]
      _ = ∑ i, ((g : Matrix (Fin N) (Fin N) K) *ᵥ v) i ^ (2 ^ f) * z₂ i := by rw [add_zero]
      _ = ∑ i, ((g : Matrix (Fin N) (Fin N) K) *ᵥ v) i ^ (2 ^ f) *
            ((g : Matrix (Fin N) (Fin N) K) *ᵥ z₂) i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← congrFun hgz₂ i]
      _ = ∑ i, v i ^ (2 ^ f) * z₂ i := hiso v z₂
      _ = 0 := horth₁ v hv z₂ hz₂
  have hyall : ∀ z : Fin N → K, ∑ i, y i ^ (2 ^ f) * z i = 0 := by
    intro z
    have hz : z ∈ cubeEigen d μ ⊔ W := by rw [hV]; exact Submodule.mem_top
    obtain ⟨z₁, hz₁, z₂, hz₂, hzsum⟩ := Submodule.mem_sup.mp hz
    have hze : z = z₁ + z₂ := hzsum.symm
    calc ∑ i, y i ^ (2 ^ f) * z i
        = ∑ i, y i ^ (2 ^ f) * (z₁ i + z₂ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hze, Pi.add_apply]
      _ = (∑ i, y i ^ (2 ^ f) * z₁ i) + ∑ i, y i ^ (2 ^ f) * z₂ i :=
            uniCubeBlock_sum_mul_add (2 ^ f) y z₁ z₂
      _ = 0 + 0 := by rw [horth₂ y hy z₁ hz₁, hyz₂ z₂ hz₂]
      _ = 0 := by rw [add_zero]
  have hy0 : y = 0 := uniCubeBlock_eq_zero_of_sum_mul_eq_zero (2 ^ f) (by positivity) hyall
  rw [← hxy, hy0, add_zero]
  exact hx


private lemma uniCubeBlock_three_ne_zero {K : Type} [Field K] [CharP K 2] : (3 : K) ≠ 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) = (2 : K) + 1 := by norm_num
  rw [h3, h2, zero_add]
  exact one_ne_zero

private noncomputable def uniCubeBlock_ePoly {K : Type} [Field K] (μ : K) : Polynomial K :=
  (Polynomial.X ^ 2 + Polynomial.C μ * Polynomial.X + Polynomial.C (μ ^ 2)) *
    Polynomial.C ((3 : K) * μ ^ 2)⁻¹

private noncomputable def uniCubeBlock_fPoly {K : Type} [Field K] (μ ω : K) : Polynomial K :=
  1 + Polynomial.C (ω - 1) * uniCubeBlock_ePoly μ

private noncomputable def uniCubeBlock_fPoly' {K : Type} [Field K] (μ ω : K) : Polynomial K :=
  1 + Polynomial.C (ω ^ 2 - 1) * uniCubeBlock_ePoly μ

private lemma uniCubeBlock_ePoly_eval_self {K : Type} [Field K] [CharP K 2] {μ : K}
    (hμ3 : μ ^ 3 = 1) : (uniCubeBlock_ePoly μ).eval μ = 1 := by
  simp only [uniCubeBlock_ePoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ3
  have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμ0
  have h3 : (3 : K) ≠ 0 := uniCubeBlock_three_ne_zero
  have h3μ2 : (3 : K) * μ ^ 2 ≠ 0 := mul_ne_zero h3 hμ2
  have hsum : μ ^ 2 + μ * μ + μ ^ 2 = (3 : K) * μ ^ 2 := by ring
  rw [hsum, mul_inv_cancel₀ h3μ2]

private lemma uniCubeBlock_ePoly_eval_of_ne {K : Type} [Field K] {μ ν : K} (hμ3 : μ ^ 3 = 1)
    (hν3 : ν ^ 3 = 1) (hνμ : ν ≠ μ) : (uniCubeBlock_ePoly μ).eval ν = 0 := by
  simp only [uniCubeBlock_ePoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  have hquad : ν ^ 2 + μ * ν + μ ^ 2 = 0 := by
    have h : (ν - μ) * (ν ^ 2 + μ * ν + μ ^ 2) = 0 := by
      have h' : (ν - μ) * (ν ^ 2 + μ * ν + μ ^ 2) = ν ^ 3 - μ ^ 3 := by ring
      rw [h', hν3, hμ3, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hνμ)
  rw [hquad, zero_mul]

private lemma uniCubeBlock_fPoly_eval_self {K : Type} [Field K] [CharP K 2] {μ ω : K}
    (hμ3 : μ ^ 3 = 1) : (uniCubeBlock_fPoly μ ω).eval μ = ω := by
  simp only [uniCubeBlock_fPoly, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, uniCubeBlock_ePoly_eval_self hμ3]
  ring

private lemma uniCubeBlock_fPoly_eval_of_ne {K : Type} [Field K] {μ ω ν : K} (hμ3 : μ ^ 3 = 1)
    (hν3 : ν ^ 3 = 1) (hνμ : ν ≠ μ) : (uniCubeBlock_fPoly μ ω).eval ν = 1 := by
  simp only [uniCubeBlock_fPoly, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, uniCubeBlock_ePoly_eval_of_ne hμ3 hν3 hνμ]
  ring

private lemma uniCubeBlock_fPoly'_eval_self {K : Type} [Field K] [CharP K 2] {μ ω : K}
    (hμ3 : μ ^ 3 = 1) : (uniCubeBlock_fPoly' μ ω).eval μ = ω ^ 2 := by
  simp only [uniCubeBlock_fPoly', Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, uniCubeBlock_ePoly_eval_self hμ3]
  ring

private lemma uniCubeBlock_fPoly'_eval_of_ne {K : Type} [Field K] {μ ω ν : K} (hμ3 : μ ^ 3 = 1)
    (hν3 : ν ^ 3 = 1) (hνμ : ν ≠ μ) : (uniCubeBlock_fPoly' μ ω).eval ν = 1 := by
  simp only [uniCubeBlock_fPoly', Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, uniCubeBlock_ePoly_eval_of_ne hμ3 hν3 hνμ]
  ring

private lemma uniCubeBlock_sum_add_add {K : Type} [Field K] [CharP K 2] {N : ℕ} (f : ℕ)
    (x y a b : Fin N → K) :
    (∑ i, (x i + y i) ^ (2 ^ f) * (a i + b i)) =
      (∑ i, x i ^ (2 ^ f) * a i) + (∑ i, y i ^ (2 ^ f) * a i) +
        (∑ i, x i ^ (2 ^ f) * b i) + ∑ i, y i ^ (2 ^ f) * b i := by
  rw [uniCubeBlock_sum_mul_add (2 ^ f) (fun i => x i + y i) a b, uniCubeBlock_sum_pow_add f x y a, uniCubeBlock_sum_pow_add f x y b]
  ring

private lemma uniCubeBlock_sum_smul_left {K : Type} [Field K] {N : ℕ} (f : ℕ) (c : K)
    (x y : Fin N → K) :
    (∑ i, (c * x i) ^ (2 ^ f) * y i) = c ^ (2 ^ f) * ∑ i, x i ^ (2 ^ f) * y i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]; ring

private lemma uniCubeBlock_sum_smul_right {K : Type} [Field K] {N : ℕ} (f : ℕ) (c : K)
    (x y : Fin N → K) :
    (∑ i, x i ^ (2 ^ f) * (c * y i)) = c * ∑ i, x i ^ (2 ^ f) * y i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private lemma uniCubeBlock_disjoint_eigen {K : Type} [Field K] {N : ℕ} {d : GL (Fin N) K}
    {μ a b : K} (hμa : μ ≠ a) (hμb : μ ≠ b) :
    Disjoint (cubeEigen d μ) (cubeEigen d a ⊔ cubeEigen d b) := by
  classical
  set M : Module.End K (Fin N → K) := Matrix.toLin' (d : Matrix (Fin N) (Fin N) K) with hM
  have hsup : ({μ, a, b} : Finset K).SupIndep M.eigenspace := M.eigenspaces_iSupIndep.supIndep' _
  have h := hsup.disjoint_sup_sup (u := ({μ} : Finset K)) (v := ({a, b} : Finset K))
    (by simp) (by simp) (by simp [hμa, hμb])
  simpa [Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty] using h

private lemma uniCubeBlock_orth_sup {K : Type} [Field K] [CharP K 2] {f N : ℕ} {d : GL (Fin N) K}
    (horth : ∀ μ' ν' : K, μ' ^ 3 = 1 → ν' ^ 3 = 1 → μ' ≠ ν' →
      ∀ v ∈ cubeEigen d μ', ∀ w ∈ cubeEigen d ν', ∑ i, v i ^ (2 ^ f) * w i = 0)
    {μ a b : K} (hμ3 : μ ^ 3 = 1) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (haμ : a ≠ μ)
    (hbμ : b ≠ μ) :
    (∀ x ∈ cubeEigen d μ, ∀ y ∈ cubeEigen d a ⊔ cubeEigen d b,
        ∑ i, x i ^ (2 ^ f) * y i = 0) ∧
      (∀ y ∈ cubeEigen d a ⊔ cubeEigen d b, ∀ x ∈ cubeEigen d μ,
        ∑ i, y i ^ (2 ^ f) * x i = 0) := by
  constructor
  · intro x hx y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    rw [show (∑ i, x i ^ (2 ^ f) * (u + v) i) = ∑ i, x i ^ (2 ^ f) * (u i + v i) from rfl,
      uniCubeBlock_sum_mul_add (2 ^ f) x u v, horth μ a hμ3 ha3 haμ.symm x hx u hu,
      horth μ b hμ3 hb3 hbμ.symm x hx v hv, add_zero]
  · intro y hy x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    rw [show (∑ i, (u + v) i ^ (2 ^ f) * x i) = ∑ i, (u i + v i) ^ (2 ^ f) * x i from rfl,
      uniCubeBlock_sum_pow_add f u v x, horth a μ ha3 hμ3 haμ u hu x hx,
      horth b μ hb3 hμ3 hbμ v hv x hx, add_zero]


private lemma uniCubeBlock_sup_eigen_eq_top {K : Type} [Field K] [Finite K] [CharP K 2]
    {q N : ℕ} (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) {d : GL (Fin N) K}
    (hd : IsHermIsometry q (d : Matrix (Fin N) (Fin N) K)) (hd3 : d ^ 3 = 1) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) = ⊤ := by
  classical
  set M : Module.End K (Fin N → K) := Matrix.toLin' (d : Matrix (Fin N) (Fin N) K) with hM
  have hdim := (uni_cube_eigen hK hq3 hd hd3).2 ω hω
  have h1ω : (1 : K) ≠ ω := fun h => hω1 h.symm
  have h1ω2 : (1 : K) ≠ ω ^ 2 := uniCubeBlock_one_ne_omega_sq hω hω1
  have hωω2 : ω ≠ ω ^ 2 := uniCubeBlock_omega_ne_sq hω
  have hABC : Disjoint (M.eigenspace 1) (M.eigenspace ω ⊔ M.eigenspace (ω ^ 2)) := by
    have hsup : ({1, ω, ω ^ 2} : Finset K).SupIndep M.eigenspace :=
      M.eigenspaces_iSupIndep.supIndep' _
    have h := hsup.disjoint_sup_sup (u := ({1} : Finset K)) (v := ({ω, ω ^ 2} : Finset K))
      (by simp) (by simp) (by simp [h1ω, h1ω2])
    simpa [Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty] using h
  have hBC : Disjoint (M.eigenspace ω) (M.eigenspace (ω ^ 2)) :=
    M.eigenspaces_iSupIndep.pairwiseDisjoint hωω2
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (M.eigenspace 1)
    (M.eigenspace ω ⊔ M.eigenspace (ω ^ 2))
  rw [hABC.eq_bot, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (M.eigenspace ω) (M.eigenspace (ω ^ 2))
  rw [hBC.eq_bot, finrank_bot, add_zero] at h2
  have hdim' : Module.finrank K ↥(M.eigenspace 1) + Module.finrank K ↥(M.eigenspace ω) +
      Module.finrank K ↥(M.eigenspace (ω ^ 2)) = N := hdim
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [Module.finrank_fin_fun, sup_assoc]
  change Module.finrank K ↥(M.eigenspace 1 ⊔ (M.eigenspace ω ⊔ M.eigenspace (ω ^ 2))) = N
  omega

private theorem uniCubeBlock_center_ne_bot {K : Type} [Field K] [Finite K] [CharP K 2]
    {f N : ℕ} (h : UnitaryFieldData 2 f K) (hN : 4 ≤ N)
    {d : GL (Fin N) K} (hd : IsHermIsometry (2 ^ f) (d : Matrix (Fin N) (Fin N) K))
    (hd3 : d ^ 3 = 1) (hq3 : 3 ∣ 2 ^ f + 1) {J' : Subgroup (PSUg N K (2 ^ f))} {μ ω : K}
    (hμ3 : μ ^ 3 = 1) (hk3 : Module.finrank K (cubeEigen d μ) = 3)
    (hJ : J' = eigBlock (2 ^ f) d μ) (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {a b : K} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (haμ : a ≠ μ) (hbμ : b ≠ μ)
    (hV : cubeEigen d μ ⊔ (cubeEigen d a ⊔ cubeEigen d b) = ⊤)
    (hdisj : Disjoint (cubeEigen d μ) (cubeEigen d a ⊔ cubeEigen d b))
    (horth : ∀ μ' ν' : K, μ' ^ 3 = 1 → ν' ^ 3 = 1 → μ' ≠ ν' →
      ∀ v ∈ cubeEigen d μ', ∀ w ∈ cubeEigen d ν', ∑ i, v i ^ (2 ^ f) * w i = 0) :
    Subgroup.center J' ≠ ⊥ := by
  classical
  set W : Submodule K (Fin N → K) := cubeEigen d a ⊔ cubeEigen d b with hW
  set M : Module.End K (Fin N → K) := Matrix.toLin' (d : Matrix (Fin N) (Fin N) K) with hM
  set zEnd : Module.End K (Fin N → K) := Polynomial.aeval M (uniCubeBlock_fPoly μ ω) with hzEnd
  set zEnd' : Module.End K (Fin N → K) := Polynomial.aeval M (uniCubeBlock_fPoly' μ ω) with hzEnd'
  have hVW : cubeEigen d μ ⊔ W = ⊤ := by rw [hW]; exact hV
  have hdisjW : Disjoint (cubeEigen d μ) W := by rw [hW]; exact hdisj
  have hω3 : ω ^ 3 = 1 := uniCubeBlock_cube_root_pow_three hω
  obtain ⟨horth1W', horth2W'⟩ :=
    uniCubeBlock_orth_sup (f := f) horth hμ3 ha3 hb3 haμ hbμ
  have horth1W : ∀ x ∈ cubeEigen d μ, ∀ y ∈ W, ∑ i, x i ^ (2 ^ f) * y i = 0 :=
    fun x hx y hy => horth1W' x hx y (hW ▸ hy)
  have horth2W : ∀ y ∈ W, ∀ x ∈ cubeEigen d μ, ∑ i, y i ^ (2 ^ f) * x i = 0 :=
    fun y hy x hx => horth2W' y (hW ▸ hy) x hx
  have hzμ : ∀ v ∈ cubeEigen d μ, zEnd v = ω • v := by
    intro v hv
    have hv' : M v = μ • v := Module.End.mem_eigenspace_iff.mp (show v ∈ M.eigenspace μ from hv)
    rw [hzEnd, Module.End.aeval_apply_of_mem_apply_eq_smul hv',
      uniCubeBlock_fPoly_eval_self hμ3]
  have hzν : ∀ ν : K, ν ^ 3 = 1 → ν ≠ μ → ∀ v ∈ cubeEigen d ν, zEnd v = v := by
    intro ν hν3 hνμ v hv
    have hv' : M v = ν • v := Module.End.mem_eigenspace_iff.mp (show v ∈ M.eigenspace ν from hv)
    rw [hzEnd, Module.End.aeval_apply_of_mem_apply_eq_smul hv',
      uniCubeBlock_fPoly_eval_of_ne hμ3 hν3 hνμ, one_smul]
  have hz'μ : ∀ v ∈ cubeEigen d μ, zEnd' v = ω ^ 2 • v := by
    intro v hv
    have hv' : M v = μ • v := Module.End.mem_eigenspace_iff.mp (show v ∈ M.eigenspace μ from hv)
    rw [hzEnd', Module.End.aeval_apply_of_mem_apply_eq_smul hv',
      uniCubeBlock_fPoly'_eval_self hμ3]
  have hz'ν : ∀ ν : K, ν ^ 3 = 1 → ν ≠ μ → ∀ v ∈ cubeEigen d ν, zEnd' v = v := by
    intro ν hν3 hνμ v hv
    have hv' : M v = ν • v := Module.End.mem_eigenspace_iff.mp (show v ∈ M.eigenspace ν from hv)
    rw [hzEnd', Module.End.aeval_apply_of_mem_apply_eq_smul hv',
      uniCubeBlock_fPoly'_eval_of_ne hμ3 hν3 hνμ, one_smul]
  have hzW : ∀ w ∈ W, zEnd w = w := by
    intro w hw
    rw [hW] at hw
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, hzν a ha3 haμ p hp, hzν b hb3 hbμ q hq]
  have hz'W : ∀ w ∈ W, zEnd' w = w := by
    intro w hw
    rw [hW] at hw
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, hz'ν a ha3 haμ p hp, hz'ν b hb3 hbμ q hq]
  have hzz' : zEnd * zEnd' = 1 := by
    apply LinearMap.ext
    intro x
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      Submodule.mem_sup.mp (show x ∈ cubeEigen d μ ⊔ W from hVW ▸ Submodule.mem_top)
    rw [Module.End.mul_apply, Module.End.one_apply, map_add, hz'μ p hp, hz'W q hq, map_add,
      map_smul, hzμ p hp, hzW q hq, smul_smul]
    rw [show ω ^ 2 * ω = 1 from by rw [← pow_succ, hω3], one_smul]
  have hz'z : zEnd' * zEnd = 1 := by
    apply LinearMap.ext
    intro x
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      Submodule.mem_sup.mp (show x ∈ cubeEigen d μ ⊔ W from hVW ▸ Submodule.mem_top)
    rw [Module.End.mul_apply, Module.End.one_apply, map_add, hzμ p hp, hzW q hq, map_add,
      map_smul, hz'μ p hp, hz'W q hq, smul_smul]
    rw [show ω * ω ^ 2 = 1 from by rw [← pow_succ', hω3], one_smul]
  have hbij : Function.Bijective zEnd := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨zEnd' y, ?_⟩⟩
    · have h := congrArg zEnd' hxy
      have h1 : zEnd' (zEnd x) = x := by
        rw [← Module.End.mul_apply, hz'z, Module.End.one_apply]
      have h2 : zEnd' (zEnd y) = y := by
        rw [← Module.End.mul_apply, hz'z, Module.End.one_apply]
      rw [h1, h2] at h
      exact h
    · rw [← Module.End.mul_apply, hzz', Module.End.one_apply]
  have hunit : IsUnit zEnd := (Module.End.isUnit_iff zEnd).mpr hbij
  let zUnit : ((Fin N → K) →ₗ[K] (Fin N → K))ˣ := hunit.unit
  have hzUnit_coe : (zUnit : Module.End K (Fin N → K)) = zEnd := IsUnit.unit_spec hunit
  let zGL : GL (Fin N) K := (Matrix.GeneralLinearGroup.toLin).symm zUnit
  have hzGL : Matrix.GeneralLinearGroup.toLin zGL = zUnit := MulEquiv.apply_symm_apply _ _
  have hzGL_coe : (↑(Matrix.GeneralLinearGroup.toLin zGL) : Module.End K (Fin N → K)) = zEnd := by
    rw [hzGL, hzUnit_coe]
  have hzv : ∀ v, (zGL : Matrix (Fin N) (Fin N) K) *ᵥ v = zEnd v := by
    intro v
    have h := congrArg (fun e : ((Fin N → K) →ₗ[K] (Fin N → K))ˣ =>
      (e : Module.End K (Fin N → K)) v) hzGL
    simpa [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply, hzUnit_coe] using h
  have hzv' : ∀ x i, ((zGL : Matrix (Fin N) (Fin N) K) *ᵥ x) i = (zEnd x) i :=
    fun x i => congrFun (hzv x) i
  have hiso : ∀ x y : Fin N → K,
      ∑ i, (zEnd x) i ^ (2 ^ f) * (zEnd y) i = ∑ i, x i ^ (2 ^ f) * y i := by
    intro x y
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      Submodule.mem_sup.mp (show x ∈ cubeEigen d μ ⊔ W from hVW ▸ Submodule.mem_top)
    obtain ⟨p', hp', q', hq', rfl⟩ :=
      Submodule.mem_sup.mp (show y ∈ cubeEigen d μ ⊔ W from hVW ▸ Submodule.mem_top)
    have hx : zEnd (p + q) = ω • p + q := by rw [map_add, hzμ p hp, hzW q hq]
    have hy : zEnd (p' + q') = ω • p' + q' := by rw [map_add, hzμ p' hp', hzW q' hq']
    rw [hx, hy]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hL : (∑ i, (ω * p i + q i) ^ (2 ^ f) * (ω * p' i + q' i)) =
        ω ^ (2 ^ f) * (ω * (∑ i, p i ^ (2 ^ f) * p' i)) + ∑ i, q i ^ (2 ^ f) * q' i := by
      rw [uniCubeBlock_sum_add_add f (fun i => ω * p i) q (fun i => ω * p' i) q']
      rw [uniCubeBlock_sum_smul_left f ω p (fun i => ω * p' i),
        uniCubeBlock_sum_smul_right f ω p p',
        uniCubeBlock_sum_smul_right f ω q p',
        uniCubeBlock_sum_smul_left f ω p q',
        horth1W p hp q' hq', horth2W q hq p' hp']
      ring
    have hR : (∑ i, (p i + q i) ^ (2 ^ f) * (p' i + q' i)) =
        (∑ i, p i ^ (2 ^ f) * p' i) + ∑ i, q i ^ (2 ^ f) * q' i := by
      rw [uniCubeBlock_sum_add_add f p q p' q',
        horth1W p hp q' hq', horth2W q hq p' hp']
      ring
    rw [hL, hR]
    have hωq : ω ^ (2 ^ f) * ω = 1 := by
      obtain ⟨m, hm⟩ := hq3
      rw [← pow_succ, hm, pow_mul, hω3, one_pow]
    rw [← mul_assoc, hωq, one_mul]
  have hle : cubeEigen d μ ≤ Submodule.comap zEnd (cubeEigen d μ) := by
    intro x hx
    rw [Submodule.mem_comap, hzμ x hx]
    exact Submodule.smul_mem _ _ hx
  have hdet : LinearMap.det zEnd = 1 := by
    rw [LinearMap.det_eq_det_mul_det (cubeEigen d μ) zEnd hle]
    have h1 : LinearMap.det (zEnd.restrict hle) = 1 := by
      have hre : zEnd.restrict hle = ω • (1 : Module.End K ↥(cubeEigen d μ)) := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        change zEnd (v : Fin N → K) = ω • (v : Fin N → K)
        exact hzμ (v : Fin N → K) v.2
      rw [hre, LinearMap.det_smul, Module.End.one_eq_id, LinearMap.det_id, hk3, mul_one, hω3]
    have h2 : LinearMap.det ((cubeEigen d μ).mapQ (cubeEigen d μ) zEnd hle) = 1 := by
      have hq : (cubeEigen d μ).mapQ (cubeEigen d μ) zEnd hle = 1 := by
        apply LinearMap.ext
        intro y
        refine Submodule.Quotient.induction_on (cubeEigen d μ) y fun x => ?_
        rw [Submodule.mapQ_apply, Module.End.one_eq_id, LinearMap.id_apply, Submodule.Quotient.eq]
        obtain ⟨p, hp, q, hq, rfl⟩ :=
          Submodule.mem_sup.mp (show x ∈ cubeEigen d μ ⊔ W from hVW ▸ Submodule.mem_top)
        rw [map_add, hzμ p hp, hzW q hq]
        have hsub : (ω • p + q) - (p + q) = (ω - 1) • p := by
          rw [sub_eq_iff_eq_add, sub_smul, one_smul]; abel
        rw [hsub]
        exact Submodule.smul_mem _ _ hp
      rw [hq]
      exact LinearMap.det_id
    rw [h1, h2, mul_one]
  have hdetGL : (zGL : Matrix (Fin N) (Fin N) K).det = 1 := by
    rw [← LinearMap.det_toLin']
    have hto : Matrix.toLin' (zGL : Matrix (Fin N) (Fin N) K) = zEnd := by
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, hzv v]
    rw [hto, hdet]
  have hzSU : zGL ∈ LargeEvenSUGroup (Fin N) K (2 ^ f) := by
    show zGL ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K N
    rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h]
    refine ⟨hdetGL, ?_⟩
    intro x y
    rw [CFSG.LinearGroups.stdHermForm_apply, CFSG.LinearGroups.stdHermForm_apply]
    simp only [UnitaryFieldData.bar_apply, hzv']
    exact hiso x y
  have hzeig : (⟨zGL, hzSU⟩ : ↥(LargeEvenSUGroup (Fin N) K (2 ^ f))) ∈ eigSub (2 ^ f) d μ := by
    intro ν hν3 hνμ v hv
    rw [hzv v]
    exact hzν ν hν3 hνμ v hv
  have hVne : cubeEigen d μ ≠ ⊥ := by
    intro hbot
    have : Module.finrank K ↥(cubeEigen d μ) = 0 := by rw [hbot, finrank_bot]
    omega
  have hWne : W ≠ ⊥ := by
    have hdisjW' : Disjoint (cubeEigen d μ) W := hdisjW
    have h := Submodule.finrank_sup_add_finrank_inf_eq (cubeEigen d μ) W
    rw [hdisjW'.eq_bot, finrank_bot, add_zero] at h
    rw [hVW, finrank_top, Module.finrank_fin_fun, hk3] at h
    intro hbot
    have : Module.finrank K ↥W = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (cubeEigen d μ)).mp hVne
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hWne
  have hzns : zGL ∉ LargeEvenScalars (Fin N) K := by
    intro hsc
    rw [largeEvenScalars_def, MonoidHom.mem_range] at hsc
    obtain ⟨u, hu⟩ := hsc
    have hcoeeq : (zGL : Matrix (Fin N) (Fin N) K) = Matrix.scalar (Fin N) (u : K) := by
      rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]
    have hscalar : ∀ y : Fin N → K, (zGL : Matrix (Fin N) (Fin N) K) *ᵥ y = (u : K) • y := by
      intro y
      rw [hcoeeq, Matrix.scalar_apply]
      funext i
      rw [Matrix.mulVec_diagonal]
      simp only [Pi.smul_apply, smul_eq_mul]
    have hu1 : (u : K) = 1 := by
      have h1 : (u : K) • w = (1 : K) • w := by rw [one_smul, ← hscalar w, hzv w, hzW w hw]
      exact smul_left_injective K hw0 h1
    have huω : (u : K) = ω := by
      have h1 : (u : K) • v = ω • v := by rw [← hscalar v, hzv v, hzμ v hv]
      exact smul_left_injective K hv0 h1
    exact hω1 (huω.symm.trans hu1)
  let zbar : PSUg N K (2 ^ f) :=
    LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ f)) ⟨zGL, hzSU⟩
  have hzbar_mem : zbar ∈ J' := by
    rw [hJ]
    exact Subgroup.mem_map.mpr ⟨⟨zGL, hzSU⟩, hzeig, rfl⟩
  have hcomm : ∀ g : ↥(LargeEvenSUGroup (Fin N) K (2 ^ f)), g ∈ eigSub (2 ^ f) d μ →
      (g : GL (Fin N) K) * zGL = zGL * (g : GL (Fin N) K) := by
    intro g hg
    set gEnd : Module.End K (Fin N → K) :=
      (Matrix.GeneralLinearGroup.toLin (g : GL (Fin N) K) : Module.End K (Fin N → K)) with hgEnd
    have hgEnd_apply : ∀ y, gEnd y = ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ y := by
      intro y
      rw [hgEnd, Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
    have hfixW : ∀ z ∈ W, ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ z = z := by
      intro z hz
      rw [hW] at hz
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hz
      rw [Matrix.mulVec_add, hg a ha3 haμ p hp, hg b hb3 hbμ q hq]
    have hgq : ∀ y ∈ W, gEnd y = y := fun y hy => by rw [hgEnd_apply y]; exact hfixW y hy
    have hgp : ∀ y ∈ cubeEigen d μ, gEnd y ∈ cubeEigen d μ := fun y hy => by
      rw [hgEnd_apply y]
      exact uniCubeBlock_mulVec_mem_cubeEigen_of_fixed h hVW horth1W horth2W g.2 hfixW hy
    have hcommEnd : zEnd * gEnd = gEnd * zEnd := by
      apply LinearMap.ext
      intro x
      obtain ⟨p, hp, q, hq, rfl⟩ :=
        Submodule.mem_sup.mp (show x ∈ cubeEigen d μ ⊔ W from hVW ▸ Submodule.mem_top)
      have hL : (zEnd * gEnd) (p + q) = ω • gEnd p + q := by
        rw [Module.End.mul_apply, map_add, hgq q hq, map_add, hzμ (gEnd p) (hgp p hp),
          hzW q hq]
      have hR : (gEnd * zEnd) (p + q) = ω • gEnd p + q := by
        rw [Module.End.mul_apply, map_add, hzμ p hp, hzW q hq, map_add, map_smul, hgq q hq]
      rw [hL, hR]
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    rw [← hgEnd, hzGL_coe]
    exact hcommEnd.symm
  have hzbar_center : (⟨zbar, hzbar_mem⟩ : ↥J') ∈ Subgroup.center ↥J' := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : PSUg N K (2 ^ f)) * zbar = zbar * (y : PSUg N K (2 ^ f))
    have hy : (y : PSUg N K (2 ^ f)) ∈ eigBlock (2 ^ f) d μ := by
      rw [← hJ]; exact y.2
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    rw [show (y : PSUg N K (2 ^ f)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ f)) g from hgy.symm]
    show LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ f)) g *
        LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ f)) ⟨zGL, hzSU⟩ =
      LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ f)) ⟨zGL, hzSU⟩ *
        LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ f)) g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcomm g hg
  have hzbar_ne_one : (⟨zbar, hzbar_mem⟩ : ↥J') ≠ 1 := by
    intro h1
    have hz1 : zbar = 1 := congrArg Subtype.val h1
    have hmem : (⟨zGL, hzSU⟩ : ↥(LargeEvenSUGroup (Fin N) K (2 ^ f))) ∈
        (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ f)) :=
      (QuotientGroup.eq_one_iff (⟨zGL, hzSU⟩ : ↥(LargeEvenSUGroup (Fin N) K (2 ^ f)))).mp hz1
    exact hzns (Subgroup.mem_subgroupOf.mp hmem)
  intro hbot
  have hmem : (⟨zbar, hzbar_mem⟩ : ↥J') ∈ (⊥ : Subgroup ↥J') := hbot ▸ hzbar_center
  exact hzbar_ne_one (by simpa using hmem)

end Helpers

theorem uniR_cube_block {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hN : 4 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J') {d : GL (Fin N) K}
    (hd : IsHermIsometry q (d : Matrix (Fin N) (Fin N) K)) (hd3 : d ^ 3 = 1) (hδ : IsConjBy d δ') :
    ∃ μ : K, μ ^ 3 = 1 ∧ J' = eigBlock q d μ ∧ CubeBlockQS q d μ ∧
      2 ≤ Module.finrank K (cubeEigen d μ) ∧ Module.finrank K (cubeEigen d μ) < N ∧
      (4 ≤ q → N ≤ Module.finrank K (cubeEigen d μ) + 2) ∧
      Nonempty (J' ⧸ Subgroup.center J' ≃* PSUg (Module.finrank K (cubeEigen d μ)) K q) ∧
      (Module.finrank K (cubeEigen d μ) = 3 → Subgroup.center J' ≠ ⊥) := by
  classical
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  obtain ⟨μ, hμ3, hJ⟩ := uni_cube_component_eq_eigBlock hK hq3 hN hd hd3 hδ hR.comp
  have hJmem : ∀ x, x ∈ J' ↔ InCubeBlock d μ x := fun x => by rw [hJ, mem_eigBlock_iff]
  have hQS : CubeBlockQS (2 ^ f) d μ :=
    (uni_cube_eigBlock_quasisimple_iff hK hq3 hN hd hd3 hμ3).mp
      (show CFSG.Assembly.IsQuasisimple ↥(eigBlock (2 ^ f) d μ) from hJ ▸ hR.comp.2.2)
  have hk2 : 2 ≤ Module.finrank K (cubeEigen d μ) := by
    rcases hQS with ⟨h2, -⟩ | h4 <;> omega
  have h3dvd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [hsq]
    exact dvd_mul_of_dvd_left hq3 _
  obtain ⟨ω, hω, hω1⟩ := CFSG.RankThree.PartTwo.Sec21.Hering214.exists_primitive_cube_root h3dvd
  have hω3 : ω ^ 3 = 1 := uniCubeBlock_cube_root_pow_three hω
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have h1ω : (1 : K) ≠ ω := fun hh => hω1 hh.symm
  have h1ω2 : (1 : K) ≠ ω ^ 2 := uniCubeBlock_one_ne_omega_sq hω hω1
  have hωω2 : ω ≠ ω ^ 2 := uniCubeBlock_omega_ne_sq hω
  have hother : 4 ≤ 2 ^ f → ∀ β : K, β ^ 3 = 1 → β ≠ μ →
      Module.finrank K (cubeEigen d β) ≤ 1 := by
    intro hq4 β hβ3 hβne
    by_contra hle
    simp only [not_le] at hle
    exact uniCubeBlock_no_second_block hK hq3 hN hd hd3 hδ hR.uniq hμ3 hJmem hk2 hβ3 hβne hle hq4
  have hNle : 4 ≤ 2 ^ f → N ≤ Module.finrank K (cubeEigen d μ) + 2 := by
    intro hq4
    have hdim := (uni_cube_eigen hK hq3 hd hd3).2 ω hω
    rcases uniCubeBlock_cube_root_eq_one_or_sq hω μ hμ3 with hμ1 | hμω | hμω2
    · rw [hμ1]
      have ha : Module.finrank K (cubeEigen d ω) ≤ 1 := hother hq4 ω hω3 (by rw [hμ1]; exact hω1)
      have hb : Module.finrank K (cubeEigen d (ω ^ 2)) ≤ 1 :=
        hother hq4 (ω ^ 2) hω23 (by rw [hμ1]; exact h1ω2.symm)
      omega
    · rw [hμω]
      have ha : Module.finrank K (cubeEigen d 1) ≤ 1 :=
        hother hq4 1 (by norm_num) (by rw [hμω]; exact h1ω)
      have hb : Module.finrank K (cubeEigen d (ω ^ 2)) ≤ 1 :=
        hother hq4 (ω ^ 2) hω23 (by rw [hμω]; exact hωω2.symm)
      omega
    · rw [hμω2]
      have ha : Module.finrank K (cubeEigen d 1) ≤ 1 :=
        hother hq4 1 (by norm_num) (by rw [hμω2]; exact h1ω2)
      have hb : Module.finrank K (cubeEigen d ω) ≤ 1 :=
        hother hq4 ω hω3 (by rw [hμω2]; exact hωω2)
      omega
  have hk_le : Module.finrank K (cubeEigen d μ) ≤ N := by
    have hle := Submodule.finrank_le (cubeEigen d μ)
    rwa [Module.finrank_fin_fun] at hle
  have hkN : Module.finrank K (cubeEigen d μ) < N := by
    refine lt_of_le_of_ne hk_le ?_
    intro hk_eq
    have htop : cubeEigen d μ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact hk_eq
    have hsubtop : eigSub (2 ^ f) d μ = ⊤ := by
      ext g
      constructor
      · intro _; trivial
      · intro _
        intro ν hν hνμ v hv
        have hbot : cubeEigen d ν = ⊥ := by
          rw [← inf_top_eq (cubeEigen d ν), ← htop]
          exact (Module.End.eigenspaces_iSupIndep
            (Matrix.toLin' (d : Matrix (Fin N) (Fin N) K))).pairwiseDisjoint hνμ |>.eq_bot
        rw [hbot, Submodule.mem_bot] at hv
        rw [hv]; simp
    have hblocktop : eigBlock (2 ^ f) d μ = ⊤ := by
      rw [eigBlock, hsubtop]
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr
        (QuotientGroup.mk'_surjective ((LargeEvenScalars (Fin N) K).subgroupOf
          (LargeEvenSUGroup (Fin N) K (2 ^ f))))
    have hJtop : J' = ⊤ := by rw [hJ, hblocktop]
    have hfixtop : ggAutFixedSubgroup δ' = ⊤ := by
      apply top_le_iff.mp
      rw [← hJtop]
      exact hR.comp.1
    have hone : δ' = 1 := by
      ext r
      have hr : r ∈ ggAutFixedSubgroup δ' := hfixtop ▸ trivial
      have hlt := (CFSG.StandardType.mem_ggAutFixedSubgroup (σ := δ') (r := r)).mp hr
      simpa using hlt
    exact hR.ne_one hone
  have hcenter : Nonempty (J' ⧸ Subgroup.center J' ≃*
      PSUg (Module.finrank K (cubeEigen d μ)) K (2 ^ f)) := by
    rw [hJ]
    exact uni_cube_eigBlock_centerQuot hK hq3 hN hd hd3 hμ3
  refine ⟨μ, hμ3, hJ, hQS, hk2, hkN, hNle, hcenter, ?_⟩
  intro hk3
  have hWall : cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) = ⊤ :=
    uniCubeBlock_sup_eigen_eq_top hK hq3 hd hd3 hω hω1
  have horth := (uni_cube_eigen hK hq3 hd hd3).1
  rcases uniCubeBlock_cube_root_eq_one_or_sq hω μ hμ3 with hμ1 | hμω | hμω2
  · rw [hμ1] at hμ3 hk3 hJ
    refine uniCubeBlock_center_ne_bot (a := ω) (b := ω ^ 2) h hN hd hd3 hq3 hμ3 hk3 hJ hω hω1
      hω3 hω23 hω1 h1ω2.symm ?_ ?_ horth
    · rw [show cubeEigen d 1 ⊔ (cubeEigen d ω ⊔ cubeEigen d (ω ^ 2)) =
          cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) from by ac_rfl]
      exact hWall
    · exact uniCubeBlock_disjoint_eigen h1ω h1ω2
  · rw [hμω] at hμ3 hk3 hJ
    refine uniCubeBlock_center_ne_bot (a := 1) (b := ω ^ 2) h hN hd hd3 hq3 hμ3 hk3 hJ hω hω1
      (by norm_num) hω23 h1ω hωω2.symm ?_ ?_ horth
    · rw [show cubeEigen d ω ⊔ (cubeEigen d 1 ⊔ cubeEigen d (ω ^ 2)) =
          cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) from by ac_rfl]
      exact hWall
    · exact uniCubeBlock_disjoint_eigen hω1 hωω2
  · rw [hμω2] at hμ3 hk3 hJ
    refine uniCubeBlock_center_ne_bot (a := 1) (b := ω) h hN hd hd3 hq3 hμ3 hk3 hJ hω hω1
      (by norm_num) hω3 h1ω2 hωω2 ?_ ?_ horth
    · rw [show cubeEigen d (ω ^ 2) ⊔ (cubeEigen d 1 ⊔ cubeEigen d ω) =
          cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) from by ac_rfl]
      exact hWall
    · exact uniCubeBlock_disjoint_eigen h1ω2.symm hωω2.symm

end CFSG.StandardType.TablePThreeKG

end
