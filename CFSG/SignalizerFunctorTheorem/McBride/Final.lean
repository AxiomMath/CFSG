module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.TheoremA

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isFunctor_of_isSignalizerFunctor {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) {Θ : Subgroup G → Subgroup G} (hΘ : IsSignalizerFunctor p 1 A Θ) :
    IsFunctor p A (fun a => Θ (Subgroup.zpowers a)) where
  le_centralizer a ha ha1 := by
    rw [← centralizer_zpowers]
    exact hΘ.central _ (zpowers_mem_E1 hp hA ha ha1)
  coprime a ha ha1 := hΘ.coprime _ (zpowers_mem_E1 hp hA ha ha1)
  normalized a ha ha1 := hΘ.normalized _ (zpowers_mem_E1 hp hA ha ha1)
  balance a ha ha1 b hb hb1 := by
    rw [← centralizer_zpowers]
    exact hΘ.balanced _ (zpowers_mem_E1 hp hA ha ha1) _ (zpowers_mem_E1 hp hA hb hb1)

theorem mcBrideRankOneTheoremAt_of_odd
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    McBrideRankOneTheoremAt p := by
  intro G _ _ A hA hlarge Θ hΘ hK
  set θ : G → Subgroup G := fun a => Θ (Subgroup.zpowers a) with hθdef
  have hθ : IsFunctor p A θ := isFunctor_of_isSignalizerFunctor hp hA hΘ
  have hC : ∀ a ∈ A, a ≠ 1 → signalizerMcBrideHypothesisB p (θ a) :=
    fun a ha ha1 => hK _ (zpowers_mem_E1 hp hA ha ha1)
  obtain ⟨W, ⟨hWA, hWcop, hWc, hWB⟩, hWmax⟩ := theoremA hp hp2 hA hlarge hθ hC
  have hval : ∀ S ∈ signalizerFunctorEk p 1 A,
      Θ S ∈ signalizers p A θ (signalizerMcBrideHypothesisB p) := by
    intro S hS
    refine ⟨hΘ.normalized S hS, hΘ.coprime S hS, fun a ha ha1 => ?_, hK S hS⟩
    change Θ S ⊓ Subgroup.centralizer {a} ≤ Θ (Subgroup.zpowers a)
    rw [← centralizer_zpowers]
    exact hΘ.balanced S hS _ (zpowers_mem_E1 hp hA ha ha1)
  have hle : completion p 1 A Θ ≤ W := completion_le fun S hS => hWmax _ (hval S hS)
  have hge : W ≤ completion p 1 A Θ := by
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p 1 hp
      A W hA (by simpa using hlarge.trans' (Nat.pow_le_pow_right hp.pos (by norm_num))) hWA hWcop
    rw [← hgen]
    refine iSup₂_le fun S hS => ?_
    obtain ⟨a, haS, ha1⟩ := exists_ne_one_of_mem_E1 hp hS
    have hSa : Subgroup.zpowers a = S :=
      eq_zpowers_of_card_eq_prime hp (by rw [hS.2, pow_one]) haS ha1
    have ha : a ∈ A := hS.1 haS
    calc W ⊓ Subgroup.centralizer (S : Set G)
        = W ⊓ Subgroup.centralizer {a} := by rw [← hSa, centralizer_zpowers]
      _ ≤ θ a := hWc a ha ha1
      _ = Θ S := by rw [hθdef]; exact congrArg Θ hSa
      _ ≤ completion p 1 A Θ := le_completion hS
  have hWeq : completion p 1 A Θ = W := le_antisymm hle hge
  refine ⟨⟨by rw [hWeq]; exact hWcop, fun S hS => le_antisymm ?_ ?_⟩, by rw [hWeq]; exact hWB⟩
  · obtain ⟨a, haS, ha1⟩ := exists_ne_one_of_mem_E1 hp hS
    have hSa : Subgroup.zpowers a = S :=
      eq_zpowers_of_card_eq_prime hp (by rw [hS.2, pow_one]) haS ha1
    rw [hWeq, ← hSa, centralizer_zpowers]
    exact hWc a (hS.1 haS) ha1
  · exact le_inf (le_completion hS) (hΘ.central S hS)

theorem mcBrideRankOneTheorem :
    McBrideRankOneTheorem := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    exact mcBrideRankOneTheoremAt_two
  · exact mcBrideRankOneTheoremAt_of_odd hp h2

end CFSG.SignalizerFunctorTheorem.McBride
