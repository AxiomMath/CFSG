module

public import CFSG.Quasithin.EmptyFaithful.S153E51A
public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E58

section Chain

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

omit [Finite G] in
theorem le_of_isSum_zero {M' Si S S₂ : Subgroup G}
    (h : IsSumOfNatSL2ModulesN153 0 M' Si S S₂) : Si ≤ S₂ := by
  obtain ⟨β, φ, -, -, -, hφ, -⟩ := h
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
  exact (hφ ⟨x, hx⟩).1 h1

theorem s_pos (h09 : Input15309Two) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15354 cx N₁ N₂ g s) : 0 < s := by
  by_contra hs
  have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
  subst hs0
  have h54 := c.h54
  have hP : Pgp153 T M V₁ Mc g ≤ VZ T M := by
    rw [← h54.four_sup]
    exact sup_le (le_of_isSum_zero h54.four_nat₁) (le_of_isSum_zero h54.four_nat₂)
  have hY : pCoreOf 2 (Y153 Mc M) ≤ Pgp153 T M V₁ Mc g := by
    have hYN : Y153 Mc M ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
      le_normalizer_pCoreOf 2 (Y153 Mc M)
    have hUN : UH153 T M V₁ Mc ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
      ((S153E.U_le_T cx).trans ((S153E.T_le_M cx).trans (le_normalizer_Y153 Mc M))).trans
        (normalizer_le_normalizer_pCoreOf 2 _)
    unfold Pgp153
    rw [h54.one]
    exact le_pCoreOf_of_le_normalizer 2 (pCoreOf_le 2 _ |>.trans le_sup_left) (sup_le hYN hUN)
      (pCoreOf_isPGroup 2 _)
  have hlt := h09 G T Mc M cx.c.hyp
  exact absurd (hlt.trans_le (hY.trans hP)) (lt_irrefl _)

end Chain

end S153E58

end CFSG.Quasithin
