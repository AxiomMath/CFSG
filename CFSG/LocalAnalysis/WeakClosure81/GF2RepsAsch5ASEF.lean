module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF
import CFSG.Quasithin.Background.E1SolvProduct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

theorem inFForAS_top_of_inE {Q : Type} [Group Q] [Finite Q] (j : ℕ) {T : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hE : E1.InE j (⊤ : Subgroup Q))
    (hU : HasUniqueMaxOver T) (hO : CFSG.pCore 2 Q = ⊥) : InFForAS j (⊤ : Subgroup Q) T := by
  intro Ω hΩ hne hbot
  obtain ⟨M, hMtop, hM⟩ := hU
  have h1 : E1.eGen j ⊤ T Ω ⊔ normalizer (E1.weakClosure T Ω : Set Q) = ⊤ := by
    have := hE T (CFSG.ABGLocalTools.isSylowOf_iff.mp hT) Ω hΩ
    rwa [top_inf_eq] at this
  have hTN : T ≤ normalizer (E1.weakClosure T Ω : Set Q) := E1.le_normalizer_weakClosure hΩ
  have hNlt : normalizer (E1.weakClosure T Ω : Set Q) < ⊤ :=
    normalizer_weakClosure_lt_top hT hΩ hne hbot hO
  have hNM : normalizer (E1.weakClosure T Ω : Set Q) ≤ M := hM _ hTN hNlt
  have hET : E1.eGen j ⊤ T Ω ⊔ T = ⊤ := by
    by_contra hne'
    have hlt : E1.eGen j ⊤ T Ω ⊔ T < ⊤ := lt_top_iff_ne_top.mpr hne'
    have hX : E1.eGen j ⊤ T Ω ⊔ T ≤ M := hM _ le_sup_right hlt
    have htop : (⊤ : Subgroup Q) ≤ M := by
      rw [← h1]
      exact sup_le (le_sup_left.trans hX) hNM
    exact absurd (lt_of_lt_of_le hMtop htop) (lt_irrefl _)
  have hnorm : T ≤ normalizer (E1.eGen j ⊤ T Ω : Set Q) := E1.le_normalizer_eGen j hΩ
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ T hnorm, hET]

theorem inFAS_top_of_inE {Q : Type} [Group Q] [Finite Q] (j : ℕ) (hE : E1.InE j (⊤ : Subgroup Q))
    (hU : ∃ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧ HasUniqueMaxOver T)
    (hO : CFSG.pCore 2 Q = ⊥) : InFAS j (⊤ : Subgroup Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀, hU₀⟩ := hU
  intro T hT
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  exact inFForAS_top_of_inE j hT' hE (hasUniqueMaxOver_of_isSylowOf hT₀ hT' hU₀) hO

end CFSG.LocalAnalysis.WeakClosure81

end
