module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

@[expose] def IsE22LieType (k : ℕ) (X : Type) [Group X] : Prop :=
  IsBenderOf k X ∨ IsPSL 3 2 k X ∨ IsPSp4 2 k X

@[expose] def HasE22LieQuot {Γ : Type} [Group Γ] (K : Subgroup Γ) : Prop :=
  ∃ (X : Type) (_ : Group X) (f : ↥K →* X), Function.Surjective f ∧
    ∃ k : ℕ, 2 ≤ k ∧ IsE22LieType k X

theorem isE22LieType_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {k : ℕ}
    (h : IsE22LieType k Y) : IsE22LieType k X := by
  rcases h with ⟨hk, h | h | h⟩ | h | h
  · exact Or.inl ⟨hk, Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)⟩
  · exact Or.inl ⟨hk, Or.inr (Or.inl (CFSG.SectionRank.suzukiModel_of_mulEquiv e h))⟩
  · exact Or.inl ⟨hk, Or.inr (Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))⟩
  · exact Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))

variable {Γ : Type} [Group Γ]

theorem HasE22LieQuot.of_surjective {K : Subgroup Γ} {Y : Type} [Group Y] (g : ↥K →* Y)
    (hg : Function.Surjective g) {k : ℕ} (hk : 2 ≤ k) (h : IsE22LieType k Y) :
    HasE22LieQuot K :=
  ⟨Y, inferInstance, g, hg, k, hk, h⟩

theorem HasE22LieQuot.of_surjective_hom {K : Subgroup Γ} {Γ' : Type} [Group Γ']
    {K' : Subgroup Γ'} (h : HasE22LieQuot K) (g : ↥K' →* ↥K) (hg : Function.Surjective g) :
    HasE22LieQuot K' := by
  obtain ⟨X, _, f, hf, k, hk, ht⟩ := h
  exact ⟨X, inferInstance, f.comp g, hf.comp hg, k, hk, ht⟩

theorem HasE22LieQuot.map_mulEquiv {Γ' : Type} [Group Γ'] (φ : Γ ≃* Γ') {K : Subgroup Γ}
    (h : HasE22LieQuot K) : HasE22LieQuot (K.map φ.toMonoidHom) :=
  h.of_surjective_hom (φ.subgroupMap K).symm.toMonoidHom (φ.subgroupMap K).symm.surjective

theorem hasE22LieQuot_map_mulEquiv_iff {Γ' : Type} [Group Γ'] (φ : Γ ≃* Γ') {K : Subgroup Γ} :
    HasE22LieQuot (K.map φ.toMonoidHom) ↔ HasE22LieQuot K := by
  refine ⟨fun h => ?_, fun h => h.map_mulEquiv φ⟩
  have h' := h.map_mulEquiv φ.symm
  have hK : (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id K
    ext x
    simp
  rwa [hK] at h'

@[expose] noncomputable def starRestrict (M : Subgroup Γ) {H K : Subgroup Γ} (hKH : K ≤ H) :
    ↥K →* ↥(star M H K) :=
  ((QuotientGroup.mk' ((kerIn M H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (star M H K) fun k => ⟨⟨(k : Γ), hKH k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩

theorem surjective_starRestrict (M : Subgroup Γ) {H K : Subgroup Γ} (hKH : K ≤ H) :
    Function.Surjective (starRestrict M hKH) := by
  rintro ⟨_, ⟨x, hx, rfl⟩⟩
  refine ⟨⟨(x : Γ), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem hasE22LieQuot_of_star {M H K : Subgroup Γ} (hKH : K ≤ H) {k : ℕ} (hk : 2 ≤ k)
    (h : IsE22LieType k ↥(star M H K)) : HasE22LieQuot K :=
  HasE22LieQuot.of_surjective (starRestrict M hKH) (surjective_starRestrict M hKH) hk h

end E2

end CFSG.Quasithin
