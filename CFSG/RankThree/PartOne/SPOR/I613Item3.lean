module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG CFSG.RankThree.PartOne.N143
open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem card_smallRee_model
    {T : Type} [Group T] {ℓ f : ℕ} (hf : f = 3) (h : ReeTitsModel T .twistedG2 ℓ f) :
    Nat.card T = (3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1) := by
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T ℓ f h
  obtain ⟨-, a', hfa', F, _, _, hF, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP F G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hF
  obtain ⟨E⟩ := hiso a' F hfa hF hw
  have hF' : Nat.card F = 3 ^ (2 * a' + 1) := by rw [hF, hfa]
  have ha1 : a' = 1 := by omega
  subst ha1
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, hΓ, -⟩ := small_Ree_Borel_coset_Sylow_action 1 F hF' w₀ hw₀
  rw [Nat.card_congr E.toEquiv, hΓ]

end CFSG.RankThree.PartOne.SPOR
