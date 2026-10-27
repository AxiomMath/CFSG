module

public import CFSG.Quasithin.Background.JonesParshallCurtisClassify

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open scoped Matrix

theorem card_G5 : Nat.card G5 = 9999360 := by
  have hdet : ∀ g : GL (Fin 5) (ZMod 2), (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1 := by
    intro g
    have h : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    generalize (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = a at h ⊢
    revert a
    decide
  let e : G5 ≃ GL (Fin 5) (ZMod 2) :=
    { toFun := Matrix.SpecialLinearGroup.toGL
      invFun := fun g => ⟨g, hdet g⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Units.ext (Matrix.SpecialLinearGroup.coe_GL_coe_matrix _) }
  rw [Nat.card_congr e, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_five]
  norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]

variable {V : Type*} [CommGroup V]

@[expose] def mulAutAdd : MulAut V →* AddMonoid.End (Additive V) where
  toFun f := (MulEquiv.toAdditive f).toAddMonoidHom
  map_one' := rfl
  map_mul' _ _ := rfl

@[reducible] noncomputable def zmod2Module (h2 : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, h2, ofMul_one]

section Rep

variable [Module (ZMod 2) (Additive V)] {H : Subgroup (MulAut V)}

noncomputable abbrev repOfIso (φ : ↥H ≃* G5) : Representation (ZMod 2) G5 (Additive V) :=
  repOfEnd (mulAutAdd.comp (H.subtype.comp φ.symm.toMonoidHom))

theorem repOfIso_apply_iso (φ : ↥H ≃* G5) (h : ↥H) (v : V) :
    repOfIso φ (φ h) (Additive.ofMul v) = Additive.ofMul ((h : MulAut V) v) := by
  change mulAutAdd ((φ.symm (φ h) : ↥H) : MulAut V) (Additive.ofMul v) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem isSimpleRep_repOfIso [Nontrivial V] (φ : ↥H ≃* G5)
    (hirr : ∀ W : Subgroup V, (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    IsSimpleRep (repOfIso φ) := by
  refine ⟨inferInstance, fun W hW => ?_⟩
  let W' : Subgroup V :=
    { carrier := {v | Additive.ofMul v ∈ W}
      mul_mem' := fun ha hb => W.add_mem ha hb
      one_mem' := W.zero_mem
      inv_mem' := fun ha => W.neg_mem ha }
  have hinv : ∀ h ∈ H, ∀ w ∈ W', (h : MulAut V) w ∈ W' := by
    intro h hh w hw
    have := hW (φ ⟨h, hh⟩) (Additive.ofMul w) hw
    rw [repOfIso_apply_iso] at this
    exact this
  rcases hirr W' hinv with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : Additive.toMul x ∈ W' := hx
    rw [h, Subgroup.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hx'
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : Additive.toMul x ∈ W' := h ▸ Subgroup.mem_top _
    exact hx'

end Rep

theorem exists_wedge_coords
    [Finite V] (h2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 10)
    {H : Subgroup (MulAut V)} (φ : ↥H ≃* G5)
    (hirr : ∀ W : Subgroup V, (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (e : V ≃ (Fin 10 → ZMod 2)) (γ : ↥H ≃* G5), e 1 = 0 ∧
      ∀ (h : ↥H) (v : V), e ((h : MulAut V) v) = wedgeRep (γ h) (e v) := by
  let _ : Module (ZMod 2) (Additive V) := zmod2Module h2
  have : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  have hsimple := isSimpleRep_repOfIso φ hirr
  have hfin : Module.finrank (ZMod 2) (Additive V) = 10 := by
    have : Fintype (Additive V) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    change Nat.card V = _ at h
    rw [hcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  obtain ⟨β, θ, hβ⟩ : ∃ (β : Additive V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)) (θ : G5 ≃* G5),
      ∀ g v, β (repOfIso φ g v) = wedgeRep (θ g) (β v) := by
    rcases classify_ten hsimple hfin with ⟨β, hβ⟩ | ⟨β, hβ⟩
    · exact ⟨β, MulEquiv.refl _, hβ⟩
    · exact ⟨β, twistα, hβ⟩
  refine ⟨Additive.ofMul.trans β.toEquiv, φ.trans θ, ?_, fun h v => ?_⟩
  · change β (Additive.ofMul 1) = 0
    rw [ofMul_one, map_zero]
  · change β (Additive.ofMul ((h : MulAut V) v)) = wedgeRep (θ (φ h)) (β (Additive.ofMul v))
    rw [← repOfIso_apply_iso φ h v, hβ]

end CFSG.Quasithin.H13.Orbit
