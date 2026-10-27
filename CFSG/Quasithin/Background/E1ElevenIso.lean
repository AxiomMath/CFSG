module

public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.E1Sec7

public section

namespace CFSG.Quasithin.E1.Eleven

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.E1

variable {G G' : Type*} [Group G] [Group G']

theorem map_conjSub_mulEquiv (e : G ≃* G') (h : G) (A : Subgroup G) :
    (conjSub h A).map e.toMonoidHom = conjSub (e h) (A.map e.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨e a, ⟨a, ha, rfl⟩, by simp [MulAut.conj_apply]⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨h * a * h⁻¹, ⟨a, ha, rfl⟩, by simp [MulAut.conj_apply]⟩

theorem isInvColl_map_mulEquiv (e : G ≃* G') {H : Subgroup G} {Ω : Set (Subgroup G)}
    (h : IsInvColl H Ω) : IsInvColl (H.map e.toMonoidHom) (Subgroup.map e.toMonoidHom '' Ω) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact Subgroup.map_mono (h.le A hA)
  · rintro _ ⟨A, hA, rfl⟩
    exact isElemAbelian_map' _ (h.isElemAbelian A hA)
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨g, hg, rfl⟩
    refine ⟨conjSub g A, h.conj A hA g hg, ?_⟩
    rw [map_conjSub_mulEquiv]
    rfl

theorem image_map_symm (e : G ≃* G') (Ω : Set (Subgroup G)) :
    Subgroup.map e.symm.toMonoidHom '' (Subgroup.map e.toMonoidHom '' Ω) = Ω := by
  ext A
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩
    rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G by
      ext; simp, Subgroup.map_id]
  · intro hA
    refine ⟨A.map e.toMonoidHom, ⟨A, hA, rfl⟩, ?_⟩
    rw [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G by
      ext; simp, Subgroup.map_id]

theorem map_map_symm (e : G ≃* G') (H : Subgroup G) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G by
    ext; simp, Subgroup.map_id]

variable [Finite G] [Finite G']

theorem inEFor_map_mulEquiv (e : G ≃* G') {i : ℕ} {H T : Subgroup G} (h : InEFor i H T) :
    InEFor i (H.map e.toMonoidHom) (T.map e.toMonoidHom) := by
  intro Ω' hΩ'
  set Ω := Subgroup.map e.symm.toMonoidHom '' Ω' with hΩdef
  have hΩ : IsInvColl H Ω := by
    have := isInvColl_map_mulEquiv e.symm hΩ'
    rwa [map_map_symm] at this
  have hΩ' : Ω' = Subgroup.map e.toMonoidHom '' Ω := by
    have := image_map_symm e.symm Ω'
    rw [MulEquiv.symm_symm] at this
    exact this.symm
  have key := congrArg (Subgroup.map e.toMonoidHom) (h Ω hΩ)
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ e.injective, Subgroup.map_equiv_normalizer_eq,
    ← eGen_map_image, ← weakClosure_map_image, ← hΩ'] at key
  exact key

theorem inE_map_mulEquiv (e : G ≃* G') {i : ℕ} {H : Subgroup G} (h : InE i H) :
    InE i (H.map e.toMonoidHom) := by
  intro T' hT'
  have hT : IsSylowIn 2 (T'.map e.symm.toMonoidHom) H := by
    have := (isSylowIn_map_mulEquiv e.symm (P := T') (H := H.map e.toMonoidHom)).mpr hT'
    rwa [map_map_symm] at this
  have := inEFor_map_mulEquiv e (h _ hT)
  have e2 : (T'.map e.symm.toMonoidHom).map e.toMonoidHom = T' := by
    have := map_map_symm e.symm T'
    rwa [MulEquiv.symm_symm] at this
  rwa [e2] at this

theorem nParam_map_mulEquiv (e : G ≃* G') (H : Subgroup G) :
    nParam (H.map e.toMonoidHom) = nParam H := by
  have hcard : Nat.card ↥(H.map e.toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective e.injective
  have hiff : ∀ i, InE i (H.map e.toMonoidHom) ↔ InE i H := fun i =>
    ⟨fun h' => by
      have := inE_map_mulEquiv e.symm h'
      rwa [map_map_symm] at this, inE_map_mulEquiv e⟩
  unfold nParam
  rw [hcard]
  simp only [hiff]

theorem nParam_top_mulEquiv (e : G ≃* G') :
    nParam (⊤ : Subgroup G) = nParam (⊤ : Subgroup G') := by
  rw [← nParam_map_mulEquiv e ⊤, Subgroup.map_top_of_surjective _ e.surjective]

end CFSG.Quasithin.E1.Eleven
