module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixI
public import CFSG.LocalAnalysis.WeakClosure81.EightDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightOne
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

@[expose] def NormalizersInMTwo {G : Type*} [Group G] (V H W : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup 2 X →
    X ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (W : Set G) →
    Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (X : Set G) →
    H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)

@[expose] def W3Lem86_1Two (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ normalizer (V : Set G)) → E3.wClos V 0 T ≠ V →
    (CentralizersInM V H T ∨ NormalizersInMTwo V H (E3.wClos V 0 T)) →
    H = (H ⊓ normalizer (V : Set G)) ⊔ (H ⊓ normalizer (E3.wClos V 0 T : Set G)) ∧
      ¬ H ≤ normalizer (V : Set G)

variable {G : Type} [Group G] [Finite G]

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem wClos_eq (h86 : W3Lem86_1Two G) (hB : Asc80ThmB)
    (hMult : SchurMultiplierInput) (h122 : W3Lem122Two) (hS : Std15 G) (h : Cex15 M V₀ V U S) :
    E3.wClos V₀ 0 S = V₀ := by
  by_contra hne
  have hH := h.hyp
  have hNV : normalizer (V₀ : Set G) = M := hH.normalizer₀
  have hWS : E3.wClos V₀ 0 S ≤ S := E3.wClos_le 0 S
  have hV₀W : V₀ ≤ E3.wClos V₀ 0 S :=
    E3.le_wClos ⟨h.V₀_le_S, 1, (conjSubgroup_one V₀).symm.le, by
      rw [conjSubgroup_one]
      exact E3.mQuot_self V₀⟩
  have hHyp7 : Hyp7 V₀ := by
    refine ⟨hH.elemAbelian₀, ?_, hH.isTI⟩
    rw [card_eq_two_pow_mSub hH.elemAbelian₀.isPGroup]
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ mSub V₀ := Nat.pow_lt_pow_right (by norm_num) h.one_lt_mSub
  have hnot0 : ¬ IsCalH0 V₀ (centralizer (U : Set G)) := fun h0 =>
    h.not_le_pCoreOf_centralizer hB hMult h122 hS h0.2
  have hsyl : IsSylowIn 2 S (centralizer (U : Set G) ⊓ normalizer (V₀ : Set G)) := by
    rw [hNV, inf_comm]
    exact h.sylow
  have hii : NormalizersInMTwo V₀ (centralizer (U : Set G)) (E3.wClos V₀ 0 S) := by
    intro X hX1 hX2 hXle hXN
    rw [hNV] at hXN ⊢
    exact inf_le_right.trans
      (normalizer_le_of_inCalU h.uniqueMax_normalizer_wClos hXN hX1 hX2)
  obtain ⟨hdec, -⟩ := h86 V₀ (centralizer (U : Set G)) S hHyp7 (h.isCalH hS) hnot0 hsyl hne
    (Or.inr hii)
  have hW1 : E3.wClos V₀ 0 S ≠ ⊥ := fun hb => hH.ne_bot (le_bot_iff.1 (hb ▸ hV₀W))
  have hW2 : IsPGroup 2 (E3.wClos V₀ 0 S) := h.sylow.isPGroup.to_le hWS
  have hWle : E3.wClos V₀ 0 S ≤
      normalizer (V₀ : Set G) ⊓ normalizer (E3.wClos V₀ 0 S : Set G) :=
    le_inf (hWS.trans (h.S_le_M.trans hNV.ge)) Subgroup.le_normalizer
  have hWN : centralizer (U : Set G) ⊓ normalizer (E3.wClos V₀ 0 S : Set G) ≤
      normalizer (V₀ : Set G) := hii _ hW1 hW2 hWle inf_le_right
  apply h.not_le
  calc centralizer (U : Set G)
      = (centralizer (U : Set G) ⊓ normalizer (V₀ : Set G)) ⊔
        (centralizer (U : Set G) ⊓ normalizer (E3.wClos V₀ 0 S : Set G)) := hdec
    _ ≤ normalizer (V₀ : Set G) := sup_le inf_le_right hWN
    _ = M := hNV

end Cex15

end CFSG.LocalAnalysis.WeakClosure81
