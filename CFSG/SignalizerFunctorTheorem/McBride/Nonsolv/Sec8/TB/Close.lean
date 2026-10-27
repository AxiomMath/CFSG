module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.Member
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Final
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Fix

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace TB

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K F₁ F₂ : Subgroup G}

theorem false_of_twoLines
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) : False := by
  have hΩ := isRegFam_omegaFam h hB hT
  have hB₀A : F₁ ⊔ F₂ ≤ A := sup_le hT.mem₁.1 hT.mem₂.1
  have hB₀ne : F₁ ⊔ F₂ ≠ ⊥ := h.ne_bot_of_mem_E2 (hT.mem_E2_sup h)
  have hcardW : Nat.card (sSup (Msig p A θ) : Subgroup G) = Nat.card K ^ p ^ 2 := by
    have h1 := hΩ.card_eq_pow (m := Nat.card K) fun X hX => card_omegaFam_member h hB hT hX
    rwa [card_omegaFam h hB hT] at h1
  have hcop : Nat.Coprime p (Nat.card (sSup (Msig p A θ) : Subgroup G)) := by
    rw [hcardW]
    refine Nat.Coprime.pow_right _ ?_
    rw [← Nat.card_congr (nonempty_mulEquiv_sup h hB hT).some.toEquiv]
    exact h.isFunctor.coprime_thetaOf hB₀A hB₀ne
  have hHB : signalizerMcBrideHypothesisB p (sSup (Msig p A θ)) :=
    T81.hypB_of_isDirectProduct h.prime (h.hypB_thetaOf hT.mem₁.1 (h.ne_bot_of_mem_E1 hT.mem₁))
      (thetaOf_anti le_sup_left) hΩ.isDirectProduct
      (fun X hX => nonempty_mulEquiv_omegaFam h hB hT hX) hcop
  refine h.false_of_inf_centralizer_eq h.normalizes_sSup_msig hcop hHB fun a ha ha1 => ?_
  by_cases haE : a ∈ E
  · exact inf_centralizer_eq_apply_of_mem h hB hT haE ha1
  · exact inf_centralizer_eq_apply_of_not_mem h hB hT ha haE ha1

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
