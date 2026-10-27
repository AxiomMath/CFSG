module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Closure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Core
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Kernel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.OrderNe
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon Subgroup

theorem not_isTransvection_of_simple {B : Type} [CommGroup B] [Finite B]
    (hB : ∀ b : B, b ^ 2 = 1) {H : Subgroup (MulAut B)} (hH : ⁅H, H⁆ = H) {S : Type} [Group S]
    [IsSimpleGroup S] (hS : OrdData (Nat.card S) ∨ Nat.card S = 504) (f : ↥H →* S)
    (hf : Function.Surjective f) (hker : f.ker ≤ center ↥H) {s : MulAut B}
    (hsN : s ∈ normalizer (H : Set (MulAut B))) (hsH : ∃ h ∈ H, s * h * s⁻¹ ≠ h) :
    ¬ UniquenessMaximal.IsTransvection s := by
  intro hs
  have hgen : H ≤ conjClosure H s := le_conjClosure_of_simple hH hsN f hf hker hsH
  have hH1 : H ≠ ⊥ := by
    intro hbot
    obtain ⟨h, hh, hne⟩ := hsH
    rw [hbot, Subgroup.mem_bot] at hh
    subst hh
    exact hne (by simp)
  obtain ⟨T, _, _, ψ, hψ, hψk, hTnab, W, _, _, c, hW, hc, hcard, hperm⟩ :=
    exists_mcLaughlin_quotient hB hH hH1 hs hsN hgen
  haveI : Finite (MulAut B) := Finite.of_injective _ MulEquiv.toEquiv_injective
  haveI : Finite S := Finite.of_surjective f hf
  have hSnab := exists_mul_ne_of_ordData hS
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ker hf hker (fun N hN h4 => eq_bot_of_pow_four hSnab hN h4)
    hψ (center_eq_bot_of_isSimpleGroup hTnab) hψk
  have hST : Nat.card S = Nat.card T := Nat.card_congr e.toEquiv
  rcases hS with hS | hS
  · exact false_of_ordData_of_isMcLaughlinGroup hW hS hc (by rw [hST]; exact hcard) hperm
  · exact false_of_card_504_of_isMcLaughlinGroup hW hc (by rw [← hS, hST]; exact hcard)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
