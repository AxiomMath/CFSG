module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionTop

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGControlsStrongFusion.exists_sylow_normalizer_le {W : Type} [Group W] [Finite W] {p : ℕ}
    {H E : Subgroup W} (hp : p.Prime) (h : GGControlsStrongFusion H E) (hE : IsElemAbelian p E)
    {K : Subgroup W} (hEK : E ⊓ K ≠ ⊥) :
    ∃ S : Subgroup W, S ≤ K ∧ IsPGroup p S ∧ ¬ p ∣ S.relIndex K ∧ E ⊓ K ≤ S ∧ S ≤ H ∧
      Subgroup.normalizer (S : Set W) ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  have hU : IsPGroup p ↥((E ⊓ K).subgroupOf K) := fun g =>
    ⟨1, by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hE.2 _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp g.2)).1⟩
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hU
  set S : Subgroup W := (P : Subgroup K).map K.subtype with hSdef
  have hSK : S ≤ K := Subgroup.map_subtype_le _
  have hSp : IsPGroup p S := P.isPGroup'.map _
  have hsub : S.subgroupOf K = (P : Subgroup K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hidx : ¬ p ∣ S.relIndex K := by
    rw [Subgroup.relIndex, hsub]
    exact P.not_dvd_index
  have hES : E ⊓ K ≤ S := by
    intro x hx
    exact ⟨⟨x, (Subgroup.mem_inf.mp hx).2⟩, hP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEK
  have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  have heE : e ∈ E := (Subgroup.mem_inf.mp he).1
  have heS : e ∈ S := hES he
  have hSH : S ≤ H := h.le_of_isPGroup heE he1' hSp heS
  refine ⟨S, hSK, hSp, hidx, hES, hSH, fun g hg => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set W) := Subgroup.inv_mem _ hg
  have hconj : g⁻¹ * e * g ∈ S := by
    have h' := (Subgroup.mem_normalizer_iff.mp hg' e).mp heS
    rwa [inv_inv] at h'
  exact h.mem_of_conj_mem heE he1' (hSH hconj)

@[expose] def GGKGroupFusionDefiningInnerInput : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (p : ℕ) (H E : Subgroup W) (d : TauCeti.ValidLieTypeIndex),
    p = d.1.characteristic → GGHypThreeSixteen p H E →
      LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ → ¬ CFSG.generalizedFitting W ≤ H →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          E ⊓ CFSG.generalizedFitting W ≠ ⊥ →
            ∀ S : Subgroup W, S ≤ CFSG.generalizedFitting W → IsPGroup p S →
              ¬ p ∣ S.relIndex (CFSG.generalizedFitting W) → S ≤ H →
                Subgroup.normalizer (S : Set W) ≤ H → GGFusionException p H E

@[expose] def GGKGroupFusionDefiningOuterInput : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (p : ℕ) (H E : Subgroup W) (d : TauCeti.ValidLieTypeIndex),
    p = d.1.characteristic → GGHypThreeSixteen p H E →
      LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ → ¬ CFSG.generalizedFitting W ≤ H →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          E ⊓ CFSG.generalizedFitting W = ⊥ → GGFusionException p H E

theorem ggKGroupFusionAt_lieDefining_of (h₁ : GGKGroupFusionDefiningInnerInput)
    (h₂ : GGKGroupFusionDefiningOuterInput) : GGKGroupFusionAt GGKFLieDefining := by
  rintro W _ _ p H E i ⟨d, rfl, hpd⟩ hyp hL hKH he
  by_cases hEK : E ⊓ CFSG.generalizedFitting W = ⊥
  · exact h₂ W p H E d hpd hyp hL hKH he hEK
  · obtain ⟨S, hSK, hSp, hSidx, -, hSH, hNH⟩ :=
      hyp.1.2.2.2.2.exists_sylow_normalizer_le hyp.1.1 hyp.1.2.2.1 hEK
    exact h₁ W p H E d hpd hyp hL hKH he hEK S hSK hSp hSidx hSH hNH

end CFSG.StandardType
