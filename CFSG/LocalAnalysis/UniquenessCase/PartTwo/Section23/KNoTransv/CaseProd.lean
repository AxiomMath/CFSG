module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdDichotomy
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdSwap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdPreserve
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon Subgroup

theorem not_isTransvection_of_prod {B : Type} [CommGroup B] [Finite B] (hB : ∀ b : B, b ^ 2 = 1)
    {H : Subgroup (MulAut B)} (hH : ⁅H, H⁆ = H) {S₀ : Type} [Group S₀] [IsSimpleGroup S₀]
    (hS : OrdData (Nat.card S₀) ∨ Nat.card S₀ = 504) (f : ↥H →* S₀ × S₀)
    (hf : Function.Surjective f) (hker : f.ker ≤ center ↥H) {s : MulAut B}
    (hsN : s ∈ normalizer (H : Set (MulAut B))) (hsH : ∃ h ∈ H, s * h * s⁻¹ ≠ h) :
    ¬ UniquenessMaximal.IsTransvection s := by
  haveI : Finite (MulAut B) := Finite.of_injective _ MulEquiv.toEquiv_injective
  haveI : Finite S₀ := Finite.of_surjective (Prod.fst ∘ f) (Prod.fst_surjective.comp hf)
  have hS₀ := exists_mul_ne_of_ordData hS
  rcases conj_prod_cases hS₀ f hf hker hsN with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
  · exact not_isTransvection_of_preserve hB hH hS f hf hker hsH h₁ h₂
  · exact not_isTransvection_of_swap hB hH hS₀ f hf hker hsN h₁

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
