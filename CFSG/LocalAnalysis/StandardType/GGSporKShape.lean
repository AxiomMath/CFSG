module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatAssembly
public import CFSG.LocalAnalysis.StandardType.GGSporKFAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKFSporadicBM (i : TauCeti.CFSGIndex) (_ : ℕ) : Prop :=
  i = .sporadic .B ∨ i = .sporadic .M

@[expose] def GGKFSporadicRest (i : TauCeti.CFSGIndex) (_ : ℕ) : Prop :=
  ∃ s, i = .sporadic s ∧ s ≠ .B ∧ s ≠ .M

theorem GGKGroupFusionAtFlatK.of_cover {S S₁ S₂ : TauCeti.CFSGIndex → ℕ → Prop}
    (hcov : ∀ i p, S i p → S₁ i p ∨ S₂ i p) (h₁ : GGKGroupFusionAtFlatK S₁)
    (h₂ : GGKGroupFusionAtFlatK S₂) : GGKGroupFusionAtFlatK S := by
  intro W _ _ hW p H E i hi hyp hL hK he
  rcases hcov i p hi with h | h
  · exact h₁ W hW p H E i h hyp hL hK he
  · exact h₂ W hW p H E i h hyp hL hK he

theorem ggKGroupFusionAtFlatK_sporadic_of_halves (hBM : GGKGroupFusionAtFlatK GGKFSporadicBM)
    (h24 : GGKGroupFusionAtFlatK GGKFSporadicRest) : GGKGroupFusionAtFlatK GGKFSporadic := by
  refine GGKGroupFusionAtFlatK.of_cover (S₁ := GGKFSporadicBM) (S₂ := GGKFSporadicRest)
    (fun i p h => ?_) hBM h24
  obtain ⟨s, rfl⟩ := h
  by_cases hB : s = .B
  · exact Or.inl (Or.inl (by rw [hB]))
  by_cases hM : s = .M
  · exact Or.inl (Or.inr (by rw [hM]))
  exact Or.inr ⟨s, rfl, hB, hM⟩

@[expose] def GGKGroupFusionAtFlatKPair (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  GGKGroupFusionAtFlatK fun i q => i = .sporadic s ∧ q = p

theorem GGKGroupFusionAtFlatK.of_pairs {S : TauCeti.CFSGIndex → ℕ → Prop}
    (hS : ∀ i p, S i p → GGKFSporadic i p)
    (h : ∀ s p, S (.sporadic s) p → GGKGroupFusionAtFlatKPair s p) : GGKGroupFusionAtFlatK S := by
  intro W _ _ hW p H E i hi hyp hL hK he
  obtain ⟨s, rfl⟩ := hS i p hi
  exact h s p hi W hW p H E (.sporadic s) ⟨rfl, rfl⟩ hyp hL hK he

end CFSG.StandardType

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Assembly

theorem ggSporK_isKGroup_of_fstar {W K : Type} [Group W] [Finite W] [Group K]
    (hW : CFSG.Open.IsKGroup W) (e : ↥(CFSG.generalizedFitting W) ≃* K) :
    CFSG.Open.IsKGroup K :=
  (hW.subgroup (CFSG.generalizedFitting W)).of_injective e.symm.toMonoidHom e.symm.injective

theorem ggSporK_pair_of_not_sq_dvd (s : TauCeti.SporadicName) (p : ℕ)
    (h : ¬ p ^ 2 ∣ Nat.card (MulAut (TauCeti.CFSGIndex.sporadic s).Group)) :
    GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨e⟩ := he
  refine (h ?_).elim
  have h2 : Nat.card E = q ^ 2 := hyp.1.2.2.2.1
  exact h2 ▸ (Subgroup.card_subgroup_dvd_card E).trans (ggSporK_card_dvd_aut hyp e)

end CFSG.StandardType.SporadicShape
