module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42.Am

section Aut

variable {D D' : Type} [Group D] [Group D']

theorem congr_conj (e : D ≃* D') (x : D) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.conj_apply]

theorem autStab_map (e : D ≃* D') (P : Subgroup D) :
    autStab (P.map e.toMonoidHom) = (autStab P).map (MulAut.congr e).toMonoidHom := by
  ext φ
  rw [Subgroup.mem_map_equiv]
  show (∀ y : D', y ∈ P.map e.toMonoidHom ↔ φ y ∈ P.map e.toMonoidHom) ↔
    ∀ x : D, x ∈ P ↔ ((MulAut.congr e).symm φ) x ∈ P
  simp only [Subgroup.mem_map_equiv, MulAut.congr_symm_apply]
  constructor
  · intro h x
    simpa using h (e x)
  · intro h y
    simpa using h (e.symm y)

end Aut

namespace LieExt

variable {D D' : Type} [Group D] [Group D'] {G : Type} [Group G] {M1 M2 : Subgroup G}

@[expose] noncomputable def congrOf (E : LieExt D M1 M2) (e : D ≃* D')
    (Mbar' : Subgroup (MulAut D')) (hM : Mbar' = E.Mbar.map (MulAut.congr e).toMonoidHom) :
    LieExt D' M1 M2 where
  Mbar := Mbar'
  TD := E.TD.map e.toMonoidHom
  P1 := E.P1.map e.toMonoidHom
  P2 := E.P2.map e.toMonoidHom
  inn_le := by
    rintro _ ⟨d, rfl⟩
    rw [hM]
    refine ⟨MulAut.conj (e.symm d), E.inn_le ⟨e.symm d, rfl⟩, ?_⟩
    show MulAut.congr e (MulAut.conj (e.symm d)) = MulAut.conj d
    rw [congr_conj, MulEquiv.apply_symm_apply]
  yam := IsYAmalgamPair.map e E.yam
  diag := by
    intro φ hφ hst
    rw [hM] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    rw [← Subgroup.map_inf_eq _ _ e.toMonoidHom e.injective, autStab_map,
      Subgroup.mem_map_iff_mem (MulAut.congr e).injective] at hst
    rw [autStab_map]
    exact Subgroup.mem_map_of_mem _ (E.diag ψ hψ hst)
  iso := by
    have h1 : (E.Mbar ⊓ autStab E.P1).map (MulAut.congr e).toMonoidHom =
        Mbar' ⊓ autStab (E.P1.map e.toMonoidHom) := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.congr e).injective, autStab_map, hM]
    have h2 : (E.Mbar ⊓ autStab E.P2).map (MulAut.congr e).toMonoidHom =
        Mbar' ⊓ autStab (E.P2.map e.toMonoidHom) := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.congr e).injective, autStab_map, hM]
    exact isoTrans E.iso (isoTrans (ofSubgroupsMapInj (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective _ _) (ofSubgroupsCongr h1 h2))

@[simp] theorem congrOf_Mbar (E : LieExt D M1 M2) (e : D ≃* D') (Mbar' : Subgroup (MulAut D'))
    (hM : Mbar' = E.Mbar.map (MulAut.congr e).toMonoidHom) : (E.congrOf e Mbar' hM).Mbar = Mbar' :=
  rfl

@[simp] theorem congrOf_TD (E : LieExt D M1 M2) (e : D ≃* D') (Mbar' : Subgroup (MulAut D'))
    (hM : Mbar' = E.Mbar.map (MulAut.congr e).toMonoidHom) :
    (E.congrOf e Mbar' hM).TD = E.TD.map e.toMonoidHom := rfl

@[simp] theorem congrOf_P1 (E : LieExt D M1 M2) (e : D ≃* D') (Mbar' : Subgroup (MulAut D'))
    (hM : Mbar' = E.Mbar.map (MulAut.congr e).toMonoidHom) :
    (E.congrOf e Mbar' hM).P1 = E.P1.map e.toMonoidHom := rfl

@[simp] theorem congrOf_P2 (E : LieExt D M1 M2) (e : D ≃* D') (Mbar' : Subgroup (MulAut D'))
    (hM : Mbar' = E.Mbar.map (MulAut.congr e).toMonoidHom) :
    (E.congrOf e Mbar' hM).P2 = E.P2.map e.toMonoidHom := rfl

@[expose] noncomputable def congr (E : LieExt D M1 M2) (e : D ≃* D') : LieExt D' M1 M2 :=
  E.congrOf e (E.Mbar.map (MulAut.congr e).toMonoidHom) rfl

@[simp] theorem congr_Mbar (E : LieExt D M1 M2) (e : D ≃* D') :
    (E.congr e).Mbar = E.Mbar.map (MulAut.congr e).toMonoidHom := rfl

@[simp] theorem congr_TD (E : LieExt D M1 M2) (e : D ≃* D') :
    (E.congr e).TD = E.TD.map e.toMonoidHom := rfl

@[simp] theorem congr_P1 (E : LieExt D M1 M2) (e : D ≃* D') :
    (E.congr e).P1 = E.P1.map e.toMonoidHom := rfl

@[simp] theorem congr_P2 (E : LieExt D M1 M2) (e : D ≃* D') :
    (E.congr e).P2 = E.P2.map e.toMonoidHom := rfl

theorem Mbar_eq_map_conj (E : LieExt D M1 M2) (x : D) :
    E.Mbar = E.Mbar.map (MulAut.congr (MulAut.conj x)).toMonoidHom := by
  have hx : MulAut.conj x ∈ E.Mbar := E.inn_le ⟨x, rfl⟩
  ext φ
  rw [Subgroup.mem_map_equiv]
  have h : (MulAut.congr (MulAut.conj x)).symm φ = (MulAut.conj x)⁻¹ * φ * MulAut.conj x := rfl
  rw [h]
  constructor
  · intro hφ
    exact E.Mbar.mul_mem (E.Mbar.mul_mem (E.Mbar.inv_mem hx) hφ) hx
  · intro hφ
    have := E.Mbar.mul_mem (E.Mbar.mul_mem hx hφ) (E.Mbar.inv_mem hx)
    simpa [mul_assoc] using this

@[expose] noncomputable def conjSylow (E : LieExt D M1 M2) (x : D) : LieExt D M1 M2 :=
  E.congrOf (MulAut.conj x) E.Mbar (E.Mbar_eq_map_conj x)

@[simp] theorem conjSylow_Mbar (E : LieExt D M1 M2) (x : D) : (E.conjSylow x).Mbar = E.Mbar :=
  rfl

@[simp] theorem conjSylow_TD (E : LieExt D M1 M2) (x : D) :
    (E.conjSylow x).TD = E.TD.map (MulAut.conj x).toMonoidHom := rfl

@[simp] theorem conjSylow_P1 (E : LieExt D M1 M2) (x : D) :
    (E.conjSylow x).P1 = E.P1.map (MulAut.conj x).toMonoidHom := rfl

@[simp] theorem conjSylow_P2 (E : LieExt D M1 M2) (x : D) :
    (E.conjSylow x).P2 = E.P2.map (MulAut.conj x).toMonoidHom := rfl

end LieExt

end CFSG.Quasithin.H13.F431
