module

public import CFSG.Milestones.ASVolI.F4N.RigExc
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F4N.L11
import all CFSG.Milestones.ASVolI.F4N.L11
public import CFSG.Milestones.ASVolI.F4N.Rig

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4n_F411Rigid_exc :
    ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → (κ = .G2d ∨ κ = .Tits) →
      ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ →
      ∀ (Y : Type) [Group Y] (μ : Cpl M₁ M₂ Y), μ.IsFaithful → Nonempty (E ≃* μ.G0) →
        Amalgam.Completion.IsQuasiEquivalent μ.toCompletion ι.toCompletion := by
  intro κ p f E _ Gp M₁ M₂ hyp hκ ι hι Y _ μ hμ he
  obtain ⟨e⟩ := he
  subst hι
  have hGp : Gp = ⊤ := hyp.canonical hκ
  subst hGp
  haveI : Finite E := hyp.finite
  have hH : (∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nonempty (↥X ≃* ↥M₁) → X = M₁) ∧
      (∀ X : Subgroup E, M₁ ⊓ M₂ ≤ X → Nonempty (↥X ≃* ↥M₂) → X = M₂) := by
    rcases hκ with rfl | rfl
    · exact burnsideF4n_overgroups_g2d hyp
    · exact burnsideF4n_overgroups_tits hyp
  have hp2 : p = 2 := by
    rcases hκ with rfl | rfl
    · obtain ⟨hp, -, -⟩ := hyp.model
      exact hp
    · obtain ⟨hp, -, -⟩ := hyp.model
      exact hp
  subst hp2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨S₀, ⟨-, hSp, hSi⟩, hB⟩, -⟩ := burnsideF4n_parabolics_at hyp
  rw [top_inf_eq, top_inf_eq] at hB
  rw [Subgroup.relIndex_top_right] at hSi
  let eY : E ≃* Y := e.trans ((MulEquiv.subgroupCongr μ.gen).trans Subgroup.topEquiv)
  exact burnsideF4n_rigid_of_overgroups hyp.gen hSp hSi hB hH.1 hH.2 μ hμ eY

end CFSG.ASVolI
