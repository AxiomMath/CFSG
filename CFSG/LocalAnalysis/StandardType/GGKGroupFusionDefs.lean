module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoKGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGKGroupFusionLayerInput : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (p : ℕ) (H E : Subgroup W),
    GGHypThreeSixteen p H E → LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ →
      H = ⊤ ∨ GGFusionException p H E

theorem ggKGroupFusionLayerInput_of_input (h : GGKGroupFusionLegacyUnrestrictedInput) :
    GGKGroupFusionLayerInput :=
  fun W _ _ p H E hyp _ => h W p H E hyp

@[expose] def GGKGroupFusionAt (S : TauCeti.CFSGIndex → ℕ → Prop) : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (p : ℕ) (H E : Subgroup W) (i : TauCeti.CFSGIndex),
    S i p → GGHypThreeSixteen p H E → LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ →
      ¬ CFSG.generalizedFitting W ≤ H →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* i.Group) → GGFusionException p H E

theorem GGKGroupFusionAt.mono {S S' : TauCeti.CFSGIndex → ℕ → Prop}
    (hS : ∀ i p, S i p → S' i p) (h : GGKGroupFusionAt S') : GGKGroupFusionAt S :=
  fun W _ _ p H E i hi hyp hL hK he => h W p H E i (hS i p hi) hyp hL hK he

theorem GGKGroupFusionAt.of_cover {S S₁ S₂ : TauCeti.CFSGIndex → ℕ → Prop}
    (hcov : ∀ i p, p.Prime → p ≠ 2 → S i p → S₁ i p ∨ S₂ i p) (h₁ : GGKGroupFusionAt S₁)
    (h₂ : GGKGroupFusionAt S₂) : GGKGroupFusionAt S := by
  intro W _ _ p H E i hi hyp hL hK he
  rcases hcov i p hyp.1.1 hyp.1.2.1 hi with h | h
  · exact h₁ W p H E i h hyp hL hK he
  · exact h₂ W p H E i h hyp hL hK he

theorem ggKGroupFusionAt_false : GGKGroupFusionAt fun _ _ => False :=
  fun _ _ _ _ _ _ _ hi => hi.elim

@[expose] def GGKFCyclic (i : TauCeti.CFSGIndex) (_ : ℕ) : Prop :=
  ∃ (q : ℕ) (hq : q.Prime), i = .cyclic q hq

@[expose] def GGKFAlternating (i : TauCeti.CFSGIndex) (_ : ℕ) : Prop :=
  ∃ (n : ℕ) (hn : 5 ≤ n), i = .alternating n hn

@[expose] def GGKFLieDefining (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p = d.1.characteristic

@[expose] def GGKFLieCross (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p ≠ d.1.characteristic

@[expose] def GGKFSporadic (i : TauCeti.CFSGIndex) (_ : ℕ) : Prop :=
  ∃ s : TauCeti.SporadicName, i = .sporadic s

theorem ggKF_cases (i : TauCeti.CFSGIndex) (p : ℕ) :
    GGKFCyclic i p ∨ GGKFAlternating i p ∨ GGKFLieDefining i p ∨ GGKFLieCross i p ∨
      GGKFSporadic i p := by
  rcases i with ⟨q, hq⟩ | ⟨n, hn⟩ | d | s
  · exact Or.inl ⟨q, hq, rfl⟩
  · exact Or.inr (Or.inl ⟨n, hn, rfl⟩)
  · by_cases hpd : p = d.1.characteristic
    · exact Or.inr (Or.inr (Or.inl ⟨d, rfl, hpd⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, rfl, hpd⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, rfl⟩)))

theorem ggKGroupFusionAt_cyclic : GGKGroupFusionAt GGKFCyclic := by
  rintro W _ _ p H E i ⟨q, hq, rfl⟩ hyp - - ⟨e⟩
  exfalso
  obtain ⟨a, b, hab⟩ := hyp.2.1.2.1
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem ggKGroupFusionAt_of_families (hA : GGKGroupFusionAt GGKFAlternating)
    (hD : GGKGroupFusionAt GGKFLieDefining) (hC : GGKGroupFusionAt GGKFLieCross)
    (hS : GGKGroupFusionAt GGKFSporadic) : GGKGroupFusionAt fun _ _ => True := by
  intro W _ _ p H E i _ hyp hL hK he
  rcases ggKF_cases i p with h | h | h | h | h
  · exact ggKGroupFusionAt_cyclic W p H E i h hyp hL hK he
  · exact hA W p H E i h hyp hL hK he
  · exact hD W p H E i h hyp hL hK he
  · exact hC W p H E i h hyp hL hK he
  · exact hS W p H E i h hyp hL hK he

theorem ggKGroupFusionAt_of_forall
    (h : ∀ i₀ : TauCeti.CFSGIndex, GGKGroupFusionAt fun i _ => i = i₀) :
    GGKGroupFusionAt fun _ _ => True :=
  fun W _ _ p H E i _ hyp hL hK he => h i W p H E i rfl hyp hL hK he

end CFSG.StandardType
