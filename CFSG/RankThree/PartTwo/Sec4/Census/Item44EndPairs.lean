module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndLin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

theorem exists_involution_pair {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
    (hk : ∃ α β : k, α ^ 2 + β ^ 2 = -1) {u v : R}
    (hu : u * u = 1 ∨ u * u = -1) (hv : v * v = 1 ∨ v * v = -1) (huv : u * v = -(v * u)) :
    ∃ u' v' : R, u' * u' = 1 ∧ v' * v' = 1 ∧ u' * v' = -(v' * u') ∧
      ∀ w : R, w * u = u * w → w * v = v * w → w * u' = u' * w ∧ w * v' = v' * w := by
  have hvu : v * u = -(u * v) := by rw [huv, neg_neg]
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact ⟨u, v, hu, hv, huv, fun w h₁ h₂ => ⟨h₁, h₂⟩⟩
  · refine ⟨u, u * v, hu, ?_, ?_, fun w h₁ h₂ => ⟨h₁, ?_⟩⟩
    · calc u * v * (u * v) = -(u * u * (v * v)) := by
            rw [mul_assoc, ← mul_assoc v, hvu, neg_mul, mul_neg]
            simp only [mul_assoc]
        _ = 1 := by rw [hu, hv, one_mul, neg_neg]
    · rw [← mul_assoc, hu, one_mul, mul_assoc, hvu, mul_neg, ← mul_assoc, hu, one_mul, neg_neg]
    · rw [← mul_assoc, h₁, mul_assoc, h₂, mul_assoc]
  · refine ⟨v, v * u, hv, ?_, ?_, fun w h₁ h₂ => ⟨h₂, ?_⟩⟩
    · calc v * u * (v * u) = -(v * v * (u * u)) := by
            rw [mul_assoc, ← mul_assoc u, huv, neg_mul, mul_neg]
            simp only [mul_assoc]
        _ = 1 := by rw [hu, hv, one_mul, neg_neg]
    · rw [← mul_assoc, hv, one_mul, mul_assoc, huv, mul_neg, ← mul_assoc, hv, one_mul, neg_neg]
    · rw [← mul_assoc, h₂, mul_assoc, h₁, mul_assoc]
  · obtain ⟨α, β, hαβ⟩ := hk
    refine ⟨α • u + β • v, β • u - α • v, ?_, ?_, ?_, fun w h₁ h₂ => ⟨?_, ?_⟩⟩
    · simp only [add_mul, mul_add, smul_mul_smul_comm, hu, hv, hvu]
      linear_combination (norm := module) -(hαβ • (1 : R))
    · simp only [sub_mul, mul_sub, smul_mul_smul_comm, hu, hv, hvu]
      linear_combination (norm := module) -(hαβ • (1 : R))
    · simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_smul_comm, hu, hv, hvu]
      module
    · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h₁, h₂]
    · simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, h₁, h₂]

theorem eq_scalar_of_commute_pairs {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {u₁ v₁ u₂ v₂ : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hu₁ : u₁ * u₁ = 1 ∨ u₁ * u₁ = -1) (hv₁ : v₁ * v₁ = 1 ∨ v₁ * v₁ = -1)
    (hu₂ : u₂ * u₂ = 1 ∨ u₂ * u₂ = -1) (hv₂ : v₂ * v₂ = 1 ∨ v₂ * v₂ = -1)
    (h₁ : u₁ * v₁ = -(v₁ * u₁)) (h₂ : u₂ * v₂ = -(v₂ * u₂)) (huu : u₁ * u₂ = u₂ * u₁)
    (huv : u₁ * v₂ = v₂ * u₁) (hvu : v₁ * u₂ = u₂ * v₁) (hvv : v₁ * v₂ = v₂ * v₁)
    {c : Matrix (Fin 4) (Fin 4) (ZMod p)} (hc₁ : c * u₁ = u₁ * c) (hc₂ : c * v₁ = v₁ * c)
    (hc₃ : c * u₂ = u₂ * c) (hc₄ : c * v₂ = v₂ * c) :
    ∃ μ : ZMod p, c = Matrix.scalar (Fin 4) μ := by
  have hk : ∃ α β : ZMod p, α ^ 2 + β ^ 2 = -1 := ZMod.sq_add_sq p (-1)
  obtain ⟨u₁', v₁', hu₁', hv₁', h₁', hw₁⟩ := exists_involution_pair hk hu₁ hv₁ h₁
  obtain ⟨u₂', v₂', hu₂', hv₂', h₂', hw₂⟩ := exists_involution_pair hk hu₂ hv₂ h₂
  obtain ⟨hu₂u₁, hu₂v₁⟩ := hw₁ u₂ huu.symm hvu.symm
  obtain ⟨hv₂u₁, hv₂v₁⟩ := hw₁ v₂ huv.symm hvv.symm
  obtain ⟨huu', huv'⟩ := hw₂ u₁' hu₂u₁.symm hv₂u₁.symm
  obtain ⟨hvu', hvv'⟩ := hw₂ v₁' hu₂v₁.symm hv₂v₁.symm
  obtain ⟨hc₁', hc₂'⟩ := hw₁ c hc₁ hc₂
  obtain ⟨hc₃', hc₄'⟩ := hw₂ c hc₃ hc₄
  exact eq_scalar_of_commute_d8d8 hp5 hu₁' hv₁' hu₂' hv₂' h₁' h₂' huu' huv' hvu' hvv' hc₁' hc₂'
    hc₃' hc₄'

end CFSG.RankThree.PartTwo.Sec4.Census
