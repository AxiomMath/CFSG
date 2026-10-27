module

public import CFSG.Quasithin.Vol2.Ch11SecKGBCa

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.C10KG

variable {Y Y' P : Type*} [Group Y] [Group Y'] [Group P]

theorem ker_comp_mulEquiv (φ : Y →* Y') (c : Y' ≃* P) :
    (c.toMonoidHom.comp φ).ker = φ.ker := by
  ext y
  simp [MonoidHom.mem_ker]

theorem isPGroup_commutator_of_mulEquiv (φ : Y →* Y') (e : Y' ≃* P) (S' : Subgroup Y')
    (h : IsPGroup 2 ↥⁅(Subgroup.normalizer ((S'.map e.toMonoidHom : Subgroup P) : Set P)).comap
      (e.toMonoidHom.comp φ), (Subgroup.normalizer ((S'.map e.toMonoidHom : Subgroup P) :
        Set P)).comap (e.toMonoidHom.comp φ)⁆) :
    IsPGroup 2 ↥⁅(Subgroup.normalizer (S' : Set Y')).comap φ,
      (Subgroup.normalizer (S' : Set Y')).comap φ⁆ := by
  have hN : (Subgroup.normalizer ((S'.map e.toMonoidHom : Subgroup P) : Set P)).comap
      (e.toMonoidHom.comp φ) = (Subgroup.normalizer (S' : Set Y')).comap φ := by
    rw [← Subgroup.comap_comap, ← Subgroup.map_equiv_normalizer_eq S' e,
      Subgroup.comap_map_eq_self_of_injective e.injective]
  rwa [hN] at h

theorem isPGroup_commutator_of_weyl_data [Finite Y] [Finite Y'] (φ : Y →* Y')
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker))
    (U : Sylow 2 Y') {A₁ A₂ : Subgroup Y'} {w : Y'}
    (hdec : ∀ b ∈ Subgroup.normalizer ((U : Subgroup Y') : Set Y'),
      ∃ u ∈ (U : Subgroup Y'), ∃ t ∈ A₁ ⊔ A₂, b = u * t)
    (hAN : A₁ ⊔ A₂ ≤ Subgroup.normalizer ((U : Subgroup Y') : Set Y'))
    (h₁ : IsCyclic A₁) (h₂ : IsCyclic A₂) (h12 : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hw₁ : ∀ a ∈ A₁, w * a * w⁻¹ = a⁻¹) (hw₂ : ∀ b ∈ A₂, w * b * w⁻¹ = b) (Q : Sylow 2 Y') :
    IsPGroup 2 ↥⁅(Subgroup.normalizer ((Q : Subgroup Y') : Set Y')).comap φ,
      (Subgroup.normalizer ((Q : Subgroup Y') : Set Y')).comap φ⁆ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y' U Q
  set d : Y' ≃* Y' := MulAut.conj g with hd
  set φ' : Y →* Y' := d.symm.toMonoidHom.comp φ with hφ'
  have hker : φ'.ker = φ.ker := ker_comp_mulEquiv φ d.symm
  have hφ's : Function.Surjective φ' := d.symm.surjective.comp hφ
  have hQ : (Q : Subgroup Y') = (U : Subgroup Y').map d.toMonoidHom := by
    rw [← hg]
    rfl
  have hN : (Subgroup.normalizer ((Q : Subgroup Y') : Set Y')).comap φ =
      (Subgroup.normalizer ((U : Subgroup Y') : Set Y')).comap φ' := by
    rw [hQ, ← Subgroup.map_equiv_normalizer_eq]
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_map_equiv]
    rfl
  rw [hN]
  refine isPGroup_commutator_comap φ' hφ's (hker ▸ hZ) (hker ▸ hodd) U.isPGroup' le_rfl hAN
    hdec ?_
  exact comap_comm_of_weyl φ' hφ's (hker ▸ hZ) (hker ▸ hodd) h₁ h₂ h12 hw₁ hw₂

end CFSG.Quasithin.Vol2.Ch11.SecB.C10KG
