module

public import CFSG.RankThree.PartOne.SEITZ5.UGen2

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem hfull_of_isTv_z [CharP K 2] (hσ : ∀ c, σ (σ c) = c) {z f : Fin n → K}
    (hzz : herm σ z z = 0) (hzf : herm σ z f ≠ 0) {M : Subgroup (SUid σ n)}
    (hTf : ∃ t ∈ M, IsTv σ t f 1) (hZ : ∀ c : fixSub σ, ∃ t ∈ M, IsTv σ t z (c : K)) :
    ∀ b : fixSub σ, ∃ t ∈ M, IsTv σ t f (b : K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨r, hrM, hr⟩ := hTf
  set η : K := herm σ f z with hη
  have hη0 : η ≠ 0 := by
    rw [hη, herm_conj σ hσ z f]
    exact (map_ne_zero σ).2 hzf
  set κ : fixSub σ := normF hσ η with hκ
  have hκ0 : κ ≠ 0 := fun h => mul_ne_zero ((map_ne_zero σ).2 hη0) hη0 (congrArg Subtype.val h)
  have hκK : (κ : K) = σ η * η := rfl
  have hrz : r • z = z + η • f := by
    rw [hr z, one_mul]
  obtain ⟨ts, htsM, hts⟩ := hZ κ⁻¹
  have hg : IsTv σ (r * ts * r⁻¹) (r • z) ((κ⁻¹ : fixSub σ) : K) := hts.conj r
  set g : SUid σ n := r * ts * r⁻¹ with hgdef
  have hgM : g ∈ M := M.mul_mem (M.mul_mem hrM htsM) (M.inv_mem hrM)
  have hz'z : herm σ (r • z) z = σ η * η := by
    rw [hrz, herm_add_left, herm_smul_left, hzz, zero_add]
  have hgz : g • z = η • f := by
    rw [hg z, hz'z, hrz]
    have hκinv : ((κ⁻¹ : fixSub σ) : K) * (σ η * η) = 1 := by
      rw [← hκK, ← Subfield.coe_mul, inv_mul_cancel₀ hκ0]
      rfl
    rw [hκinv, one_smul]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (z i) * h2
  intro b
  obtain ⟨tc, htcM, htc⟩ := hZ (b * κ⁻¹)
  refine ⟨g * tc * g⁻¹, M.mul_mem (M.mul_mem hgM htcM) (M.inv_mem hgM), ?_⟩
  have h1 := htc.conj g
  rw [hgz, isTv_smul_vec] at h1
  convert h1 using 1
  rw [Subfield.coe_mul, mul_assoc, ← hκK, ← Subfield.coe_mul, inv_mul_cancel₀ hκ0]
  simp

end CFSG.RankThree.PartOne.SEITZ5
