module

public import CFSG.Quasithin.Vol2.Ch10SecQ1Base
public import CFSG.Quasithin.Background.HMathieuNorm

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

namespace C10P01

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

theorem map_conj_stab0 {τ : Equiv.Perm (Fin 24)} (hτ : τ ∈ AutPerm) :
    (AutPerm ⊓ stab 0).map (MulAut.conj τ).toMonoidHom = AutPerm ⊓ stab (τ 0) := by
  ext σ
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_stab_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨ρ, ⟨hρ, hρ0⟩, rfl⟩
    refine ⟨AutPerm.mul_mem (AutPerm.mul_mem hτ hρ) (AutPerm.inv_mem hτ), ?_⟩
    simp [Equiv.Perm.mul_apply, hρ0]
  · rintro ⟨hσ, hσx⟩
    refine ⟨τ⁻¹ * σ * τ, ⟨AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hσ) hτ, ?_⟩, ?_⟩
    · simp [Equiv.Perm.mul_apply, hσx]
    · group

theorem map_conj_stab01 {τ : Equiv.Perm (Fin 24)} (hτ : τ ∈ AutPerm) :
    (AutPerm ⊓ stab 0 ⊓ stab 1).map (MulAut.conj τ).toMonoidHom =
      AutPerm ⊓ stab (τ 0) ⊓ stab (τ 1) := by
  ext σ
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_stab_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨ρ, ⟨⟨hρ, hρ0⟩, hρ1⟩, rfl⟩
    refine ⟨⟨AutPerm.mul_mem (AutPerm.mul_mem hτ hρ) (AutPerm.inv_mem hτ), ?_⟩, ?_⟩
    · simp [Equiv.Perm.mul_apply, hρ0]
    · simp [Equiv.Perm.mul_apply, hρ1]
  · rintro ⟨⟨hσ, hσx⟩, hσy⟩
    refine ⟨τ⁻¹ * σ * τ,
      ⟨⟨AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hσ) hτ, ?_⟩, ?_⟩, ?_⟩
    · simp [Equiv.Perm.mul_apply, hσx]
    · simp [Equiv.Perm.mul_apply, hσy]
    · group

theorem stab_props_m23
    (x : Fin 24) :
    IsSimpleGroup ↥(AutPerm ⊓ stab x) ∧ Nat.card ↥(AutPerm ⊓ stab x) = 10200960 := by
  obtain ⟨v, hv⟩ := exists_ne x
  obtain ⟨τ, hτ, h0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x v hv.symm
  have hmap := map_conj_stab0 hτ
  rw [h0] at hmap
  let e : ↥mog23 ≃* ↥(AutPerm ⊓ stab x) :=
    ((AutPerm ⊓ stab 0).equivMapOfInjective _ (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr hmap)
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M23 :=
    CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  have : IsSimpleGroup ↥mog23 := mog23EquivM23.isSimpleGroup
  exact ⟨e.symm.isSimpleGroup, (Nat.card_congr e.toEquiv).symm.trans card_mog23⟩

theorem stab_props_m22
    {x y : Fin 24} (hxy : x ≠ y) :
    IsSimpleGroup ↥(AutPerm ⊓ stab x ⊓ stab y) ∧
      Nat.card ↥(AutPerm ⊓ stab x ⊓ stab y) = 443520 := by
  obtain ⟨τ, hτ, h0, h1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  have hmap := map_conj_stab01 hτ
  rw [h0, h1] at hmap
  let e : ↥mog22 ≃* ↥(AutPerm ⊓ stab x ⊓ stab y) :=
    ((AutPerm ⊓ stab 0 ⊓ stab 1).equivMapOfInjective _ (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr hmap)
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have : IsSimpleGroup ↥mog22 := mog22EquivM22.isSimpleGroup
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr mog22EquivM22.toEquiv,
    CFSG.Sporadic.Mathieu.card_M22]

end C10P01

open C10P01

theorem factB4aM23_holds :
    FactB4aM23 := by
  intro x X _ hX π
  obtain ⟨hs, hc⟩ := stab_props_m23 x
  exact not_surjective_of_isSimpleGroup hs (hc ▸ not_shapeCard_10200960) hX π

theorem factB4aM22_holds :
    FactB4aM22 := by
  intro x y hxy X _ hX π
  obtain ⟨hs, hc⟩ := stab_props_m22 hxy
  exact not_surjective_of_isSimpleGroup hs (hc ▸ not_shapeCard_443520) hX π

end CFSG.Quasithin.Vol2.Ch10.SecA
