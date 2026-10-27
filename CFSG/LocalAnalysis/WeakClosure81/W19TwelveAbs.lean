module

public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveFit
public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveInv
public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveMin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem exists_irreducible_constituent {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {H E₁ X O V₀ : Subgroup G} (hA : IsElemAbelian 2 E₁) (hXH : X ≤ H) (hOH : O ≤ H)
    (hE₁ : H ≤ normalizer (E₁ : Set G)) (hVE : V₀ ≤ E₁)
    (hV₀ : ∀ h ∈ H, ∀ v ∈ V₀, h * v = v * h)
    (hK : H ≤ normalizer ((X ⊔ O : Subgroup G) : Set G))
    (hOE : ∀ o ∈ O, ∀ e ∈ E₁, ⁅e, o⁆ ∈ V₀) (hX : IsPGroup p X) (hnot : ¬ ⁅X, E₁⁆ ≤ V₀) :
    ∃ E₀ : Subgroup G, V₀ ≤ E₀ ∧ E₀ ≤ E₁ ∧ H ≤ normalizer (E₀ : Set G) ∧
      (∀ U : Subgroup G, V₀ ≤ U → U ≤ E₀ → H ≤ normalizer (U : Set G) → U = V₀ ∨ U = E₀) ∧
      ¬ ⁅X, E₀⁆ ≤ V₀ := by
  have hRE : ⁅E₁, X⁆ ⊔ V₀ ≤ E₁ := by
    refine sup_le (Subgroup.commutator_le.2 fun e he x hx => ?_) hVE
    have h1 : x * e⁻¹ * x⁻¹ ∈ E₁ :=
      (Subgroup.mem_normalizer_iff.1 (hE₁ (hXH hx)) e⁻¹).1 (E₁.inv_mem he)
    have h2 : ⁅e, x⁆ = e * (x * e⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact E₁.mul_mem he h1
  have hVR : V₀ < ⁅E₁, X⁆ ⊔ V₀ := by
    refine lt_of_le_of_ne le_sup_right fun h => hnot ?_
    rw [Subgroup.commutator_comm]
    exact le_sup_left.trans h.ge
  have hHR := le_normalizer_commutator_sup hXH hOH hE₁ hVE hV₀ hK hOE
  obtain ⟨E₀, hVE₀, hE₀R, hHE₀, hirr⟩ := exists_minimal_invariant hVR hHR
  refine ⟨E₀, hVE₀.le, hE₀R.trans hRE, hHE₀, hirr, fun hle => ?_⟩
  obtain ⟨u, huE₀, huV⟩ := SetLike.exists_of_lt hVE₀
  refine huV (mem_of_mem_commutator_sup hp hodd hA hVE hX (fun x hx => hE₁ (hXH hx))
    (fun x hx v hv => hV₀ x (hXH hx) v hv) (hE₀R huE₀) fun x hx => ?_)
  rw [← commutatorElement_inv]
  exact V₀.inv_mem (hle (Subgroup.commutator_mem_commutator hx huE₀))

end CFSG.LocalAnalysis.WeakClosure81

end
