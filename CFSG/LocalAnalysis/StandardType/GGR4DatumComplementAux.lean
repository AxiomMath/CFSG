module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

@[expose] def dcm_preimage {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive E ≃+ V) (W : Submodule (ZMod 3) V) : Subgroup E :=
  (W.toAddSubgroup.comap ι.toAddMonoidHom).toSubgroup'

theorem dcm_preimage_mem {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive E ≃+ V) (W : Submodule (ZMod 3) V) (b : E) :
    b ∈ dcm_preimage ι W ↔ ι (Additive.ofMul b) ∈ W := by
  rw [dcm_preimage, AddSubgroup.mem_toSubgroup', AddSubgroup.mem_comap,
    Submodule.mem_toAddSubgroup]
  rfl

@[expose] noncomputable def dcm_preimage_equiv {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive E ≃+ V) (W : Submodule (ZMod 3) V) :
    Additive ↥(dcm_preimage ι W) ≃+ W :=
  AddEquiv.ofBijective
    ((ι.toAddMonoidHom.comp ((Subgroup.subtype (dcm_preimage ι W)).toAdditive)).codRestrict W
      (fun a => by
        have ha := (Additive.toMul a).2
        rw [dcm_preimage_mem] at ha
        simpa using ha))
    ⟨fun a b hab => by
      have h1 : (Subgroup.subtype (dcm_preimage ι W)) (Additive.toMul a) =
          (Subgroup.subtype (dcm_preimage ι W)) (Additive.toMul b) := by
        apply ι.injective
        exact congrArg Subtype.val hab
      exact Additive.toMul.injective (Subgroup.subtype_injective _ h1),
     fun w => by
      refine ⟨Additive.ofMul ⟨Additive.toMul (ι.symm (w : V)), ?_⟩, ?_⟩
      · rw [dcm_preimage_mem]
        simp
      · apply Subtype.ext
        simp [AddMonoidHom.codRestrict]⟩

theorem dcm_preimage_equiv_coe {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive E ≃+ V) (W : Submodule (ZMod 3) V)
    (a : Additive ↥(dcm_preimage ι W)) :
    ((dcm_preimage_equiv ι W a : W) : V) =
      ι ((Subgroup.subtype (dcm_preimage ι W)).toAdditive a) := by
  simp [dcm_preimage_equiv, AddMonoidHom.codRestrict]

theorem dcm_congrOfMapEq_coe {E : Type} [Group E] {A B : Subgroup E}
    {e : E ≃* E} (h : Subgroup.map (e : E →* E) A = B) (a : ↥A) :
    ((TauCeti.Subgroup.congrOfMapEq e h a : ↥B) : E) = e a := by
  simp

@[expose] def dcm_stab {E : Type} [Group E] (A : Subgroup E) : Subgroup (MulAut E) where
  carrier := {e | Subgroup.map (e : E →* E) A = A}
  mul_mem' := by
    intro e f he hf
    show Subgroup.map ((e * f : MulAut E) : E →* E) A = A
    rw [show ((e * f : MulAut E) : E →* E) = (e : E →* E).comp (f : E →* E) from rfl,
      ← Subgroup.map_map, hf, he]
  one_mem' := by
    show Subgroup.map ((1 : MulAut E) : E →* E) A = A
    rw [show ((1 : MulAut E) : E →* E) = MonoidHom.id E from rfl, Subgroup.map_id]
  inv_mem' := by
    intro e he
    show Subgroup.map ((e⁻¹ : MulAut E) : E →* E) A = A
    have hcomp : ((e⁻¹ : MulAut E) : E →* E).comp (e : E →* E) = MonoidHom.id E := by
      ext x; simp
    conv_lhs => rw [← he]
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]

theorem dcm_stab_mp {E : Type} [Group E] (A : Subgroup E) {e : MulAut E}
    (h : e ∈ dcm_stab A) : Subgroup.map (e : E →* E) A = A := h

@[expose] noncomputable def dcm_restrict {E : Type} [Group E] (A : Subgroup E) :
    ↥(dcm_stab A) →* MulAut ↥A where
  toFun e := TauCeti.Subgroup.congrOfMapEq (e : MulAut E) (dcm_stab_mp A e.2)
  map_one' := by
    apply MulEquiv.ext; intro a
    apply Subtype.ext
    simp
  map_mul' := by
    intro e f
    apply MulEquiv.ext; intro a
    apply Subtype.ext
    calc ((TauCeti.Subgroup.congrOfMapEq ((e * f : ↥(dcm_stab A)) : MulAut E)
            (dcm_stab_mp A (e * f).2) a : ↥A) : E)
        = (e * f : MulAut E) a := dcm_congrOfMapEq_coe _ a
      _ = (e : MulAut E) ((f : MulAut E) a) := MulAut.mul_apply E e f a
      _ = (e : MulAut E) ((TauCeti.Subgroup.congrOfMapEq (f : MulAut E)
            (dcm_stab_mp A f.2) a : ↥A) : E) := by rw [dcm_congrOfMapEq_coe]
      _ = ((TauCeti.Subgroup.congrOfMapEq (e : MulAut E) (dcm_stab_mp A e.2)
            (TauCeti.Subgroup.congrOfMapEq (f : MulAut E) (dcm_stab_mp A f.2) a) : ↥A) : E) :=
          (dcm_congrOfMapEq_coe _ _).symm
      _ = (((TauCeti.Subgroup.congrOfMapEq (e : MulAut E) (dcm_stab_mp A e.2) *
            TauCeti.Subgroup.congrOfMapEq (f : MulAut E) (dcm_stab_mp A f.2)) a : ↥A) : E) := by
          rw [MulAut.mul_apply]

theorem dcm_restrict_coe {E : Type} [Group E] (A : Subgroup E)
    (e : ↥(dcm_stab A)) (a : ↥A) :
    ((dcm_restrict A e a : ↥A) : E) = (e : MulAut E) a := by
  simp [dcm_restrict]

theorem dcm_map_conj_eq_iff {G : Type} [Group G] {H : Subgroup G} {g : G} :
    Subgroup.map (MulAut.conj g).toMonoidHom H = H ↔ g ∈ Subgroup.normalizer (H : Set G) := by
  constructor
  · intro hmap
    have hle : H ≤ Subgroup.comap (MulAut.conj g).toMonoidHom H := by
      rw [← Subgroup.map_le_iff_le_comap]; exact le_of_eq hmap
    have hmap' : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom H = H := by
      have h := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hmap
      rw [Subgroup.map_map] at h
      have hfg : (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)).comp
          (MulEquiv.toMonoidHom (MulAut.conj g)) = MonoidHom.id G := by
        ext y
        change (MulAut.conj g⁻¹) ((MulAut.conj g) y) = y
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      rw [hfg, Subgroup.map_id] at h
      exact h.symm
    have hle' : H ≤ Subgroup.comap (MulAut.conj g⁻¹).toMonoidHom H := by
      rw [← Subgroup.map_le_iff_le_comap]; exact le_of_eq hmap'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hle hh, fun hh => by
      have h2 := hle' hh
      rw [Subgroup.mem_comap] at h2
      change (MulAut.conj g⁻¹) (g * h * g⁻¹) ∈ H at h2
      rw [MulAut.conj_apply] at h2
      rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h from by group] at h2⟩
  · intro hg
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    · intro x hx
      rw [Subgroup.mem_map]
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
      · change (MulAut.conj g) (g⁻¹ * x * g) = x
        rw [MulAut.conj_apply]; group

theorem dcm_F4_mulVec_zero (d : Fin 4 → ZMod 3)
    (h : ∀ i, ∑ k, ((CartanMatrix.F₄ i k : ℤ) : ZMod 3) * d k = 0) : d = 0 := by
  revert h d
  decide +kernel

theorem dcm_F4t_mulVec_zero (d : Fin 4 → ZMod 3)
    (h : ∀ i, ∑ k, ((CartanMatrix.F₄ k i : ℤ) : ZMod 3) * d k = 0) : d = 0 := by
  revert h d
  decide +kernel


end CFSG.StandardType

end
