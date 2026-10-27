module

public import CFSG.Monster.B.Geometry.Gallery

public section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W}

theorem eq_of_forall_apply_eq (hδ : IsWeylDistanceBuilding cs δ) {T : Set (Equiv.Perm C)}
    (hT : ∀ t ∈ T, t ∈ typeAut cs δ) {a : C} (ha : ∀ t ∈ T, t a = a)
    (hpan : ∀ (i : ι) (y : C), δ a y = cs.simple i → ∃ t ∈ T, t y ≠ y)
    {d : C} (hd : ∀ t ∈ T, t d = d) : d = a := by
  by_contra hne
  obtain ⟨ω, hω, hprod⟩ := cs.exists_isReduced (δ a d)
  obtain ⟨γ, hγ, htype, hend⟩ := exists_strictGallery hδ hω hprod.symm
  cases γ with
  | nil => exact hne hend.symm
  | cons p γ' =>
    obtain ⟨t, htT, htp⟩ := hpan p.1 p.2 hγ.1
    have hmap : IsStrictGallery cs δ (t a) (galleryMap t (p :: γ')) :=
      IsStrictGallery.map (X := Set.univ)
        (fun y _ z _ i h => (dist_typeAut hδ (hT t htT) y z).trans h) (Set.mem_univ a) hγ
        (fun _ _ => Set.mem_univ _)
    rw [ha t htT] at hmap
    have hend' : galleryEnd a (galleryMap t (p :: γ')) = galleryEnd a (p :: γ') := by
      have h := galleryEnd_galleryMap t a (p :: γ')
      rw [ha t htT, hend, hd t htT] at h
      rw [h, hend]
    have heq := eq_of_isStrictGallery hδ hmap hγ (galleryType_galleryMap t _)
      (by rw [galleryType_galleryMap, htype]; exact hω) hend'
    have h1 : (p.1, t p.2) = p := List.head_eq_of_cons_eq heq
    exact htp (congrArg Prod.snd h1)

theorem eq_one_of_commute_of_free {G : Type*} [Group G] [MulAction G C]
    (hδ : IsWeylDistanceBuilding cs δ) {T : Set G}
    (hT : ∀ t ∈ T, MulAction.toPerm t ∈ typeAut cs δ) {a : C} (ha : ∀ t ∈ T, t • a = a)
    (hpan : ∀ (i : ι) (y : C), δ a y = cs.simple i → ∃ t ∈ T, t • y ≠ y)
    {k : G} (hk : ∀ t ∈ T, k * t = t * k) (hfree : k • a = a → k = 1) : k = 1 := by
  refine hfree (eq_of_forall_apply_eq hδ (T := MulAction.toPerm '' T) ?_ ?_ ?_ ?_)
  · rintro _ ⟨t, ht, rfl⟩
    exact hT t ht
  · rintro _ ⟨t, ht, rfl⟩
    exact ha t ht
  · intro i y hy
    obtain ⟨t, ht, hty⟩ := hpan i y hy
    exact ⟨MulAction.toPerm t, ⟨t, ht, rfl⟩, hty⟩
  · rintro _ ⟨t, ht, rfl⟩
    change t • k • a = k • a
    rw [smul_smul, ← hk t ht, mul_smul, ha t ht]

end CFSG.Monster.B.TwoA.Amalgam
