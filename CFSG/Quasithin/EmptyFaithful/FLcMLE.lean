module

public import CFSG.Quasithin.EmptyFaithful.FLcL45
public import CFSG.Quasithin.Background.FLcP0Ker
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem isPSL_quotient_pCore {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL n 2 1 X) : IsPSL n 2 1 (X ⧸ CFSG.pCore 2 X) := by
  have hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X n 2 1 h).2
  obtain ⟨e⟩ := FLc.nonempty_equiv_SLt_of_isPSL h
  have hp : IsPGroup 2 ↥(CFSG.pCore 2 X) := CFSG.pCore_isPGroup (p := 2) (G := X)
  have hbot : CFSG.pCore 2 X = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X) with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hp
      have hX : IsPGroup 2 X := hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
      exact FLc.not_isPGroup_SLt hn (hX.of_equiv e)
  have e1 : X ⧸ CFSG.pCore 2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e1.symm h

theorem mle_parabolic_ne {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hE : CompTypeE15120 L) :
    IsParabolic2 L (mZ1516 Mc Z₁ ⊓ L) ∧ mZ1516 Mc Z₁ ⊓ L ≠ L := by
  have hlist : ListC15120 L := by
    rcases hE with h | h
    · exact Or.inl (isPSL_quotient_pCore (by norm_num) h)
    · exact Or.inr (isPSL_quotient_pCore (by norm_num) h)
  refine ⟨isParabolic2_mZ1516_inf hc.h18 hc.hL hlist, fun h => hc.hL.not_le ?_⟩
  calc L = mZ1516 Mc Z₁ ⊓ L := h.symm
    _ ≤ mZ1516 Mc Z₁ := inf_le_left

@[expose] def Input15120MLECent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → CompTypeE15120 L →
    L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) ≤ mZ1516 Mc Z₁ ⊓ L

theorem input15120MLE_of_cent (h : Input15120MLECent) : Input15120MLE := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hE
  obtain ⟨h1, h2⟩ := mle_parabolic_ne hc hE
  exact ⟨h1, h2, h G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hE⟩

end CFSG.Quasithin
