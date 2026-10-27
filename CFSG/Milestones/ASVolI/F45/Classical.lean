module

public import CFSG.Milestones.ASVolI.F45.Kinds
public import CFSG.Milestones.ASVolI.F45.Sp4
public import CFSG.Milestones.ASVolI.F45.U
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

theorem burnsideF45_hasSystem_Sp4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 p f Gp M₁ M₂) (hp : p.Prime) : burnsideF45_HasSystem .Sp4 p Gp := by
  obtain ⟨chart, -⟩ := hyp.toHypF_4_4g.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, marking, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K', fK', finK', charK', scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · have hc : c' = .Sp4 := by
      cases c' <;> first | rfl | exact absurd hk (by decide)
    subst hc
    haveI : Fact p.Prime := ⟨hp⟩
    have hK : Nat.card marking.field = p ^ f := by simpa using marking.field_card
    haveI : CharP marking.field p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        marking.exponent_pos hK
    exact ⟨_, inferInstance, marking.identification, 4, burnsideF45_sp4System marking.field, rfl,
      burnsideF45_sp4System_isSylow marking.field hp⟩
  all_goals exact absurd hk (by decide)

section Unitary

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un
  CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF45_hasSystem_U4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 p f Gp M₁ M₂) (hp : p.Prime) : burnsideF45_HasSystem .U4 p Gp := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨marking⟩ := burnsideF45U_nonempty_marking (c := .U4) hyp.toHypF_4_4g
  have hF : Nat.card marking.field = (p ^ f) ^ 2 := marking.field_card.trans (if_pos (Or.inl rfl))
  haveI : CharP marking.field p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : marking.field) ≠ 0) := ⟨hζ⟩
  let θ₀ : StatedProj (StatedSU 4 (p ^ f) marking.field) ≃* ↥Gp :=
    (MulEquiv.refl _ : StatedProj (StatedSU 4 (p ^ f) marking.field) ≃*
      StatedProj (nativeGroup .U4 (p ^ f) marking.field)).trans marking.identification
  exact ⟨_, inferInstance, θ₀, 4, burnsideF45U4_system hF ζ, rfl,
    burnsideF45U4_system_isSylow hF ζ⟩

theorem burnsideF45_hasSystem_U5 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 p f Gp M₁ M₂) (hp : p.Prime) : burnsideF45_HasSystem .U5 p Gp := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨marking⟩ := burnsideF45U_nonempty_marking (c := .U5) hyp.toHypF_4_4g
  have hF : Nat.card marking.field = (p ^ f) ^ 2 := marking.field_card.trans (if_pos (Or.inr rfl))
  haveI : CharP marking.field p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : marking.field) ≠ 0) := ⟨hζ⟩
  let θ₀ : StatedProj (StatedSU 5 (p ^ f) marking.field) ≃* ↥Gp :=
    (MulEquiv.refl _ : StatedProj (StatedSU 5 (p ^ f) marking.field) ≃*
      StatedProj (nativeGroup .U5 (p ^ f) marking.field)).trans marking.identification
  exact ⟨_, inferInstance, θ₀, 4, burnsideF45U5_system hF ζ, rfl,
    burnsideF45U5_system_isSylow hF ζ⟩

end Unitary

section C6


theorem burnsideF45_C6_classical {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    (hκ : κ = .Sp4 ∨ κ = .U4 ∨ κ = .U5) (hGp : Gp = ⊤) :
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v := by
  have hp := burnsideF4a_prime_of_isGenLie hyp.model
  have hP := burnsideF45_parabolics hyp.toHypF_4_4g
  have hm := burnsideF45_three_le_m κ
  rcases hκ with rfl | rfl | rfl
  · exact burnsideF45_C6_of_hasSystem hyp hp hm hGp hP (burnsideF45_hasSystem_Sp4 hyp hp)
  · exact burnsideF45_C6_of_hasSystem hyp hp hm hGp hP (burnsideF45_hasSystem_U4 hyp hp)
  · exact burnsideF45_C6_of_hasSystem hyp hp hm hGp hP (burnsideF45_hasSystem_U5 hyp hp)

end C6

end CFSG.ASVolI
