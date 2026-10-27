module

public import CFSG.Quasithin.Background.F918P3
public import CFSG.Quasithin.Background.F9Eighteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Alt

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

@[expose] def FFAlt15365 (hF : HypF918 T V L V₁ Vp H K) (W : Subgroup G) (hWU : W ≤ conjClosure Vp H) :
    Prop :=
  (IsFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W) (hF.isElemAbelian_tilde_of_le hWU) ∧
      IsFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
        (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H))
        (hF.isElemAbelian_quotient W)) ∨
    (F9.IsStrongFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W)
        (hF.isElemAbelian_tilde_of_le hWU) ∨
      F9.IsStrongFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
        (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H))
        (hF.isElemAbelian_quotient W))

end Alt

section Proof

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem tildeOf_conjClosure_ne_bot (hF : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) (hI : IsIrrPlusTilde V₁ (conjClosure K T) I) :
    tildeOf V₁ (conjClosure I H) ≠ ⊥ := by
  have h1 := hF.toHypF98.toHypF91
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  intro hbot
  have hIV₁ : I ≤ V₁ := by
    intro i hi
    have hiN : i ∈ Subgroup.normalizer (V₁ : Set G) := h1.H_normalizes_V₁ (hUH (hIU hi))
    have : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ ∈
        tildeOf V₁ (conjClosure I H) :=
      secMk_mem_secImg (x := ⟨i, hiN⟩) (le_conjClosure I H hi)
    rw [hbot] at this
    have h2 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ = 1 := this
    exact secMk_eq_one_iff.mp h2
  have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
    intro i hi
    refine ⟨hi, h1.H_normalizes_V₁ (hUH (hIU hi)), fun k hk => ?_⟩
    have h3 : k * i⁻¹ * k⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (h1.H_normalizes_V₁ (hF.K₀_le_H hk)) i⁻¹).mp
        (V₁.inv_mem (hIV₁ hi))
    have e : i * k * i⁻¹ * k⁻¹ = i * (k * i⁻¹ * k⁻¹) := by group
    rw [e]
    exact V₁.mul_mem (hIV₁ hi) h3
  exact (not_le_of_gt hI.2.2.1) hIC

end Proof

end CFSG.Quasithin
