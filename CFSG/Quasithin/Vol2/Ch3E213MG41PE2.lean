module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PE1

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)}

theorem ipl (hS : SectionSplit G₀) (hone : Refl.OnePerCentre G₀) {x y z w : Fin 4 → k}
    (hx : x ∈ Refl.normC G₀) (hy : y ∈ Refl.normC G₀) (hz : z ∈ Refl.normC G₀)
    (hw : w ∈ Refl.normC G₀) (hxy : spBil x y = 0) (hne : x ≠ y) {α β : k}
    (hzxy : z = α • x + β • y) (hwx : spBil w x ≠ 0) (hwy : spBil w y ≠ 0)
    (hwz : spBil w z ≠ 0) : α + β = 1 := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  set a := spBil w x with ha
  set b := spBil w y with hb
  set ρ := b • x + a • y with hρ
  have hyx : spBil y x = 0 := by rw [bil_symm, hxy]
  have hxρ : spBil x ρ = 0 := by
    simp only [hρ, map_add, map_smul, smul_eq_mul, bil_self, hxy, mul_zero, add_zero]
  have hyρ : spBil y ρ = 0 := by
    simp only [hρ, map_add, map_smul, smul_eq_mul, bil_self, hyx, mul_zero, add_zero]
  have hwρ : spBil w ρ = 0 := by
    simp only [hρ, map_add, map_smul, smul_eq_mul, ← ha, ← hb]
    linear_combination a * b * h0
  have hzρ : spBil z ρ = 0 := by
    simp only [hzxy, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hxρ, hyρ,
      smul_zero, add_zero]
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hyx' : y = (b / a) • x := by
      funext i
      have hi := congrFun h i
      simp only [hρ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hwx]
      linear_combination hi - (b * x i) * h0
    have h1 : b / a = 1 := Refl.eq_one_of_smul_mem hone hx (by rw [← hyx']; exact hy)
    exact hne (by rw [hyx', h1, one_smul])
  have hnot : ∀ v, spBil w v ≠ 0 → v ∉ k ∙ ρ := by
    intro v hv hmem
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    exact hv (by rw [map_smul, smul_eq_mul, hwρ, mul_zero])
  rcases hS ρ x w hρ0 hx hw hxρ hwρ hwx with hA | ⟨Q, hQadd, hQsmul, hQ1⟩
  · have hμ : b / a = 1 := by
      refine hA y hy (b / a) (div_ne_zero hwy hwx)
        (Submodule.mem_span_singleton.mpr ⟨a⁻¹, ?_⟩)
      funext i
      simp only [hρ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_add, inv_mul_cancel_left₀ hwx, div_eq_mul_inv]
      linear_combination (a⁻¹ * b * x i) * h0
    have hba : b = a := (div_eq_one_iff_eq hwx).mp hμ
    have hsum : α + β ≠ 0 := by
      intro hs
      apply hnot z hwz
      refine Submodule.mem_span_singleton.mpr ⟨β / a, ?_⟩
      rw [hzxy, hρ, hba]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_add, ← mul_assoc, ← mul_assoc, div_mul_cancel₀ β hwx]
      linear_combination (-x i) * hs + (β * x i) * h0
    refine hA z hz (α + β) hsum (Submodule.mem_span_singleton.mpr ⟨β / a, ?_⟩)
    rw [hzxy, hρ, hba]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_add, ← mul_assoc, ← mul_assoc, div_mul_cancel₀ β hwx]
    linear_combination (β * x i) * h0
  · have hQx := hQ1 x hx hxρ (hnot x hwx)
    have hQy := hQ1 y hy hyρ (hnot y hwy)
    have hQz := hQ1 z hz hzρ (hnot z hwz)
    have hxρ' : spBil (α • x) ρ = 0 := by
      rw [map_smul, LinearMap.smul_apply, hxρ, smul_zero]
    have hyρ' : spBil (β • y) ρ = 0 := by
      rw [map_smul, LinearMap.smul_apply, hyρ, smul_zero]
    rw [hzxy, hQadd _ _ hxρ' hyρ', hQsmul _ _ hxρ, hQsmul _ _ hyρ, hQx, hQy] at hQz
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hxy, mul_zero, add_zero,
      mul_one] at hQz
    exact eq_one_of_sq_eq_one (by linear_combination hQz + α * β * h0)

end CFSG.Quasithin.Ch3E213M.G41.Big
