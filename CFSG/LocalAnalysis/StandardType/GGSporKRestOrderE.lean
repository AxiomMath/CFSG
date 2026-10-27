module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped Pointwise

theorem sporKRest_cover_of_orderE {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hval : (Nat.card K).factorization p = 2) (x₀ : K) (hx₀ : x₀ ≠ 1)
    (hx₀p : IsPGroup p (Subgroup.zpowers x₀)) (hgen : ∀ x : K, IsConj x₀ x → SporKRestGenerating p x) :
    SporKRestCover p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E hE hcard
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hEp : IsPGroup p E := IsPGroup.of_card hcard
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have hS : Nat.card S = p ^ 2 := by rw [Sylow.card_eq_multiplicity, hval]
  have hEeq : E = (S : Subgroup K) := Subgroup.eq_of_le_of_card_ge hES (by rw [hS, hcard])
  obtain ⟨S₁, hS₁⟩ := hx₀p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S₁ S
  have h1 : x₀ ∈ (S₁ : Subgroup K) := hS₁ (Subgroup.mem_zpowers x₀)
  have h2 : MulAut.conj g x₀ ∈ (MulAut.conj g • (S₁ : Set K)) := Set.smul_mem_smul_set h1
  rw [← Sylow.coe_smul, hg] at h2
  have h3 : g * x₀ * g⁻¹ ∈ S := by simpa [MulAut.conj_apply] using h2
  refine ⟨g * x₀ * g⁻¹, hEeq ▸ h3, ?_, hgen _ (isConj_iff.2 ⟨g, rfl⟩)⟩
  intro h
  exact hx₀ (by simpa using h)

end CFSG.StandardType.SporadicShape
