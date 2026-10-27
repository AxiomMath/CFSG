module

public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.CGT.Timmesfeld75

@[expose] def SubpairWitnessAt (X : Type) [Group X] (T : Subgroup X) (g : X) : Prop :=
  (Group.IsSolvable ↥(T ⊔ conjSubgroup g T) ∧ ¬ IsPGroup 2 ↥(T ⊔ conjSubgroup g T)) ∨
  ∃ R : Subgroup ↥(T ⊔ conjSubgroup g T), ∃ _ : R.Normal, Group.IsSolvable ↥R ∧
    Nonempty (↥(T ⊔ conjSubgroup g T) ⧸ R ≃* alternatingGroup (Fin 5))

@[expose] def SubpairWitness (L : Type) [Group L] : Prop :=
  ∀ T : Subgroup L, CFSG.CGT.Timmesfeld75.IsWC T → 4 ≤ Nat.card T →
    ∃ g : L, SubpairWitnessAt L T g

@[expose] def GapsStatement : Prop :=
  ∀ (X : Type) [Group X], ((∃ k : ℕ, 6 ≤ k ∧ k ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin k))) ∨
    CFSG.Blueprint.NativeSporadic.IsSporadic X .M22 ∨
    CFSG.Blueprint.NativeSporadic.IsSporadic X .M23 ∨
    CFSG.Blueprint.NativeSporadic.IsSporadic X .M24) → SubpairWitness X

theorem SubpairWitnessAt.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {T : Subgroup X} {g : Y} (h : SubpairWitnessAt Y (T.map e.toMonoidHom) g) :
    ∃ g' : X, SubpairWitnessAt X T g' := by
  have hmap : (T ⊔ conjSubgroup (e.symm g) T).map e.toMonoidHom =
      T.map e.toMonoidHom ⊔ conjSubgroup g (T.map e.toMonoidHom) := by
    rw [Subgroup.map_sup, map_conjSubgroup_mulEquiv]
    simp
  let eT : ↥(T ⊔ conjSubgroup (e.symm g) T) ≃*
      ↥(T.map e.toMonoidHom ⊔ conjSubgroup g (T.map e.toMonoidHom)) :=
    (Subgroup.equivMapOfInjective _ _ e.injective).trans (MulEquiv.subgroupCongr hmap)
  rcases h with hg | ⟨R, hRnorm, hRsolv, ⟨e5⟩⟩
  · refine ⟨e.symm g, Or.inl ⟨?_, ?_⟩⟩
    · haveI : Group.IsSolvable
          ↥(T.map e.toMonoidHom ⊔ conjSubgroup g (T.map e.toMonoidHom)) := hg.1
      exact Group.isSolvable_of_surjective (f := eT.symm.toMonoidHom) eT.symm.surjective
    · intro hp
      exact hg.2 (hp.of_equiv eT)
  · let R' : Subgroup ↥(T ⊔ conjSubgroup (e.symm g) T) := R.comap eT.toMonoidHom
    have hR'map : R'.map eT.toMonoidHom = R := by
      refine Subgroup.map_comap_eq_self ?_
      rw [MonoidHom.range_eq_top.mpr eT.surjective]
      exact le_top
    let eR : ↥R' ≃* ↥R :=
      (Subgroup.equivMapOfInjective R' eT.toMonoidHom eT.injective).trans
        (MulEquiv.subgroupCongr hR'map)
    haveI : Group.IsSolvable ↥R' :=
      Group.isSolvable_of_surjective (f := eR.symm.toMonoidHom) eR.symm.surjective
    let qe : (↥(T ⊔ conjSubgroup (e.symm g) T) ⧸ R') ≃*
        (↥(T.map e.toMonoidHom ⊔ conjSubgroup g (T.map e.toMonoidHom)) ⧸ R) :=
      QuotientGroup.congr R' R eT hR'map
    exact ⟨e.symm g, Or.inr ⟨R', inferInstance, inferInstance, ⟨qe.trans e5⟩⟩⟩

theorem SubpairWitness.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SubpairWitness Y) : SubpairWitness X := by
  intro T hT h4
  have h4' : 4 ≤ Nat.card (T.map e.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  obtain ⟨g, hg⟩ := h _ (hT.map_mulEquiv e) h4'
  obtain ⟨g', hg'⟩ := SubpairWitnessAt.of_mulEquiv e hg
  exact ⟨g', hg'⟩

end CFSG.RankThree.GF2n.Tim81
