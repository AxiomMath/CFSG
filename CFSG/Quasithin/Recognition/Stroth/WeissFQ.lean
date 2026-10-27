module

public import CFSG.Quasithin.Background.F3FiniteCompletion
public import CFSG.Quasithin.Recognition.Stroth.WeissQuotient

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin
open CFSG.Quasithin.RankTwoAmalgam

universe u w

theorem exists_faithful_finite_completion_weiss {α : RankTwoAmalgam.{u}} {Y₀ : Type w}
    [Group Y₀] [Finite Y₀] (c₀ : α.Completion Y₀) (hc₀ : c₀.IsFaithful) {n : ℕ}
    (hn : 1 ≤ n) (hW : WeissMoufangHat α n) (m : ℕ) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y) (c : α.Completion Y),
      c.IsFaithful ∧ (∃ π : Y →* Y₀, π.comp c.φ1 = c₀.φ1 ∧ π.comp c.φ2 = c₀.φ2) ∧
      MoufangCondition ↥(c.φ1.range ⊔ c.φ2.range) c.graph n ∧
      WeissFree ↥(c.φ1.range ⊔ c.φ2.range) c.graph n ∧ (m : ℕ∞) < c.graph.egirth := by
  obtain ⟨Y, hY, hFin, c, hc, hπ, hgirth⟩ :=
    exists_faithful_finite_completion_lt_egirth c₀ hc₀ m
  letI : Group Y := hY
  letI : Finite Y := hFin
  exact ⟨Y, hY, hFin, c, hc, hπ, completion_moufangCondition_of_hat c hc hW.1,
    completion_weissFree_of_hat c hc hn hW.2, hgirth⟩

theorem ofSubgroups_exists_faithful_finite_completion_weiss {X : Type u} [Group X] [Finite X]
    (P1 P2 : Subgroup X) {n : ℕ} (hn : 1 ≤ n) (hW : WeissMoufangHat (ofSubgroups P1 P2) n)
    (m : ℕ) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y) (c : (ofSubgroups P1 P2).Completion Y),
      c.IsFaithful ∧ (∃ π : Y →* X, (∀ g : ↥P1, π (c.φ1 g) = (g : X)) ∧
        ∀ g : ↥P2, π (c.φ2 g) = (g : X)) ∧
      MoufangCondition ↥(c.φ1.range ⊔ c.φ2.range) c.graph n ∧
      WeissFree ↥(c.φ1.range ⊔ c.φ2.range) c.graph n ∧ (m : ℕ∞) < c.graph.egirth := by
  obtain ⟨Y, hY, hFin, c, hc, ⟨π, hπ1, hπ2⟩, hM, hWf, hgirth⟩ :=
    exists_faithful_finite_completion_weiss
      (inclusionCompletion P1 P2 (P1 ⊔ P2) rfl)
      (inclusionCompletion_isFaithful P1 P2 (P1 ⊔ P2) rfl) hn hW m
  letI : Group Y := hY
  letI : Finite Y := hFin
  refine ⟨Y, hY, hFin, c, hc, ⟨(P1 ⊔ P2).subtype.comp π, ?_, ?_⟩, hM, hWf, hgirth⟩
  · intro g
    have h : π (c.φ1 g) = (inclusionCompletion P1 P2 (P1 ⊔ P2) rfl).φ1 g :=
      DFunLike.congr_fun hπ1 g
    change ((P1 ⊔ P2).subtype (π (c.φ1 g)) : X) = (g : X)
    rw [h]
    rfl
  · intro g
    have h : π (c.φ2 g) = (inclusionCompletion P1 P2 (P1 ⊔ P2) rfl).φ2 g :=
      DFunLike.congr_fun hπ2 g
    change ((P1 ⊔ P2).subtype (π (c.φ2 g)) : X) = (g : X)
    rw [h]
    rfl

end CFSG.Quasithin.Stroth
