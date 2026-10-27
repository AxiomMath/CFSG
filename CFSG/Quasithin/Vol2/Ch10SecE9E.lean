module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10SecQ34LH

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {H K₁ K₂ : Subgroup G}
  {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}

theorem le_comap_inr_of_le_comap_inl (hc : C10P34.PairCtx H K₁ K₂ φ) {g : G}
    (h₁₂ : K₁.map (MulAut.conj g).toMonoidHom = K₂)
    (h₂₁ : K₂.map (MulAut.conj g).toMonoidHom = K₁) {R S : Subgroup G} (hRS : R ≤ S)
    (hSK : S ≤ K₁ ⊔ K₂) (hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hcard : Nat.card ((S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) =
      Nat.card ((S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)))
    (h : (S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ) ≤
      ((R.subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inl _ _)) :
    (S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ) ≤
      ((R.subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inr _ _) := by
  set β := C10P34.conjQuot K₁ K₂ g h₁₂ with hβ
  set S₁ := (S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ) with hS₁
  set S₂ := (S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ) with hS₂
  set Z₂ := ((R.subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inr _ _) with hZ₂
  have hβu : ∀ u ∈ S₁, β u ∈ Z₂ ∧ β u ∈ S₂ := by
    intro u hu
    obtain ⟨⟨w, hwK⟩, hw, hwu⟩ := h hu
    have hwR : w ∈ R := Subgroup.mem_subgroupOf.mp hw
    have hgw : g * w * g⁻¹ ∈ K₁ ⊔ K₂ := hSK (hRS (hgR w hwR))
    have hform := hc.app_conj_swap h₁₂ h₂₁ hwK hgw
    rw [hwu] at hform
    simp only [MonoidHom.inl_apply, map_one] at hform
    refine ⟨⟨⟨g * w * g⁻¹, hgw⟩, hgR w hwR, ?_⟩, ⟨⟨g * w * g⁻¹, hgw⟩, hRS (hgR w hwR), ?_⟩⟩
    · rw [hform]; rfl
    · rw [MonoidHom.comp_apply, hform]; rfl
  have hle : S₁.map β.toMonoidHom ≤ S₂ := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hβu u hu).2
  have heq : S₁.map β.toMonoidHom = S₂ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← hcard, Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective]
  rw [← heq]
  rintro _ ⟨u, hu, rfl⟩
  exact (hβu u hu).1

theorem le_comap_inl_of_le_comap_inr (hc : C10P34.PairCtx H K₁ K₂ φ) {g : G}
    (h₁₂ : K₁.map (MulAut.conj g).toMonoidHom = K₂)
    (h₂₁ : K₂.map (MulAut.conj g).toMonoidHom = K₁) {R S : Subgroup G} (hRS : R ≤ S)
    (hSK : S ≤ K₁ ⊔ K₂) (hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hcard : Nat.card ((S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) =
      Nat.card ((S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)))
    (h : (S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ) ≤
      ((R.subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inr _ _)) :
    (S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ) ≤
      ((R.subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inl _ _) := by
  set β := C10P34.conjQuot K₂ K₁ g h₂₁ with hβ
  set S₁ := (S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ) with hS₁
  set S₂ := (S.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ) with hS₂
  set Z₁ := ((R.subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inl _ _) with hZ₁
  have hβu : ∀ u ∈ S₂, β u ∈ Z₁ ∧ β u ∈ S₁ := by
    intro u hu
    obtain ⟨⟨w, hwK⟩, hw, hwu⟩ := h hu
    have hwR : w ∈ R := Subgroup.mem_subgroupOf.mp hw
    have hgw : g * w * g⁻¹ ∈ K₁ ⊔ K₂ := hSK (hRS (hgR w hwR))
    have hform := hc.app_conj_swap h₁₂ h₂₁ hwK hgw
    rw [hwu] at hform
    simp only [MonoidHom.inr_apply, map_one] at hform
    refine ⟨⟨⟨g * w * g⁻¹, hgw⟩, hgR w hwR, ?_⟩, ⟨⟨g * w * g⁻¹, hgw⟩, hRS (hgR w hwR), ?_⟩⟩
    · rw [hform]; rfl
    · rw [MonoidHom.comp_apply, hform]; rfl
  have hle : S₂.map β.toMonoidHom ≤ S₁ := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hβu u hu).2
  have heq : S₂.map β.toMonoidHom = S₁ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard, Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective]
  rw [← heq]
  rintro _ ⟨u, hu, rfl⟩
  exact (hβu u hu).1

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
