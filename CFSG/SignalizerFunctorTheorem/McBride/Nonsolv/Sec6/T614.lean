module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L611
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L612
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L67
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M6
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M7
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M4

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem theorem_6_14
    (h : Counterexample p A θ) (hS : (sSet p A θ 1).Nonempty) :
    ∃ E K : Subgroup G, sSet p A θ 2 = {E} ∧ TypeBCore p A θ E K := by
  obtain ⟨E, S⟩ := h.exists_setting614 hS
  obtain ⟨F₀, hF₀, hF₀E⟩ := S.exists_line_ne h hS
  obtain ⟨f₀, hf₀A, hf₀1, hf₀⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF₀
  have hf₀E : f₀ ∉ E := fun hmem => hF₀E (by
    rw [← hf₀]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
      (by rw [S.mem.2, h.card_zpowers hf₀A hf₀1, pow_one]))
  obtain ⟨B₀, hB₀, hEB₀, -⟩ := S.exists_complement h hf₀A hf₀E
  have hW : ∀ B ∈ signalizerFunctorEk p 2 A, E ⊓ B = ⊥ →
      wTilde θ E B = wTilde θ E B₀ := fun B hB hEB => h.wTilde_eq S hB hEB hB₀ hEB₀
  obtain ⟨hkOf, hWE⟩ := h.kOf_eq_and_wTilde_eq S hW
  obtain ⟨K, hK, hKL⟩ := h.exists_simple_K S hS hkOf
  refine ⟨E, K, S.sSet_two, ?_⟩
  refine ⟨S.mem, hK, h.lemma_6_8, h.exists_isWreath_E S hB₀ hEB₀ hWE, ?_, ?_, S.bN_eq⟩
  · intro F hF hFE
    obtain ⟨L, hL⟩ := h.lcal_thetaOf_nonempty hF.1 (h.ne_bot_of_mem_E1 hF)
    exact ⟨L, _, h.isWreath_of_mem_lcal S hkOf hF hFE hL, hKL F hF hFE L hL⟩
  · intro a ha haE
    have ha1 : a ≠ 1 := fun e => haE (e ▸ E.one_mem)
    rw [h.isFunctor.thetaOf_zpowers ha ha1]
    exact hkOf a ha haE

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
