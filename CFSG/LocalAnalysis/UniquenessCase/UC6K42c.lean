module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K42b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

@[expose] def K42Fermat : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) G V), Function.Injective ρ →
    ∀ r : ℕ, r.Prime → r ≠ p → r ≠ 2 →
    ∀ D : Subgroup G, Nat.card D = r → fixV ρ D = ⊥ →
    ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≠ ⊥ → D ≤ normalizer (Q : Set G) → ⁅D, Q⁆ = Q →
      ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k

end CFSG.LocalAnalysis.UniquenessCase.UCK

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup

theorem k42_of_fermat (h : UCK.K42Fermat) : UCK.K42 := by
  intro p hp G _ _ hK V _ _ _ ρ hρ q r hq hr hqp hrp hqr D hD hfix Q hQp hQne hDQ hcomm
  haveI : Fact p.Prime := ⟨hp⟩
  have hq2 : q = 2 := q_eq_two_uc6 ρ hρ hq hr hqp hrp hqr D hD hfix Q hQp hQne hDQ hcomm
  subst hq2
  exact ⟨fun hab => abelian_false_uc6 ρ hρ hq hqp hr D hD hfix Q hQp hQne hab hDQ hcomm, rfl,
    h p hp (Ne.symm hqp) G hK V ρ hρ r hr hrp (Ne.symm hqr) D hD hfix Q hQp hQne hDQ hcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6
