module

public import CFSG.Monster.B.Geometry.ChamberSystem

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

variable (cs δ) in
structure IsBuildingOn (J : Set ι) (R : Set C) : Prop where
  mem_parabolic : ∀ x ∈ R, ∀ y ∈ R, δ x y ∈ cs.parabolic J
  eq_one_iff : ∀ x ∈ R, ∀ y ∈ R, δ x y = 1 ↔ x = y
  mul_simple : ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, ∀ j ∈ J, δ y z = cs.simple j →
    (δ x z = δ x y ∨ δ x z = δ x y * cs.simple j) ∧
      (cs.length (δ x y * cs.simple j) = cs.length (δ x y) + 1 → δ x z = δ x y * cs.simple j)
  exists_simple : ∀ x ∈ R, ∀ y ∈ R, ∀ j ∈ J,
    ∃ z ∈ R, δ y z = cs.simple j ∧ δ x z = δ x y * cs.simple j

theorem isBuildingOn_residue (hδ : IsWeylDistanceBuilding cs δ) (J : Set ι) (a : C) :
    IsBuildingOn cs δ J (residue cs δ J a) where
  mem_parabolic x hx y hy := mem_parabolic_of_mem_residue hδ hx hy
  eq_one_iff x _ y _ := hδ.eq_one_iff x y
  mul_simple x _ y _ z _ j _ h := hδ.mul_simple x y z j h
  exists_simple x hx y hy j hj := by
    obtain ⟨z, hyz, hxz⟩ := hδ.exists_simple x y j
    refine ⟨z, ?_, hyz, hxz⟩
    rw [← residue_eq_of_mem hδ hy]
    exact Relation.ReflTransGen.single ⟨j, hj, hyz⟩

namespace IsBuildingOn

variable {J : Set ι} {R : Set C} (hB : IsBuildingOn cs δ J R)
include hB

theorem eq_one_self {x : C} (hx : x ∈ R) : δ x x = 1 := (hB.eq_one_iff x hx x hx).mpr rfl

theorem symm_of_eq_simple {x y : C} (hx : x ∈ R) (hy : y ∈ R) {j : ι} (hj : j ∈ J)
    (h : δ x y = cs.simple j) : δ y x = cs.simple j := by
  obtain ⟨z, hz, hyz, hxz⟩ := hB.exists_simple x hx y hy j hj
  rw [h, cs.simple_mul_simple_self, hB.eq_one_iff x hx z hz] at hxz
  rwa [← hxz] at hyz

theorem dist_eq {x : C} (hx : x ∈ R) {γ : List (ι × C)} (hγ : IsStrictGallery cs δ x γ)
    (hR : ∀ p ∈ γ, p.2 ∈ R) (hJ : ∀ i ∈ galleryType γ, i ∈ J)
    (hred : cs.IsReduced (galleryType γ)) :
    δ x (galleryEnd x γ) = cs.wordProd (galleryType γ) := by
  induction γ using List.reverseRecOn with
  | nil => simp [hB.eq_one_self hx]
  | append_singleton γ p ih =>
    rw [isStrictGallery_concat] at hγ
    rw [galleryType_append] at hred
    have hred' := isReduced_of_isReduced_concat hred
    have hR' : ∀ q ∈ γ, q.2 ∈ R := fun q hq => hR q (by simp [hq])
    have hJ' : ∀ i ∈ galleryType γ, i ∈ J := fun i hi => hJ i (by simp [hi])
    have h := ih hγ.1 hR' hJ' hred'
    have hlen := length_mul_simple_of_isReduced_concat hred
    rw [← h] at hlen
    have hend : galleryEnd x γ ∈ R := by
      rcases List.eq_nil_or_concat' γ with rfl | ⟨γ', q, rfl⟩
      · exact hx
      · rw [galleryEnd_concat]; exact hR' q (by simp)
    rw [galleryEnd_concat, (hB.mul_simple x hx _ hend p.2 (hR p (by simp)) p.1
      (hJ p.1 (by simp)) hγ.2).2 hlen, h, galleryType_append, cs.wordProd_append]
    simp [galleryType]

theorem exists_strictGallery {x y : C} (hx : x ∈ R) (hy : y ∈ R) {ω : List ι}
    (hω : cs.IsReduced ω) (h : cs.wordProd ω = δ x y) :
    ∃ γ : List (ι × C), IsStrictGallery cs δ x γ ∧ galleryType γ = ω ∧ galleryEnd x γ = y ∧
      ∀ p ∈ γ, p.2 ∈ R := by
  induction ω using List.reverseRecOn generalizing y with
  | nil =>
    rw [cs.wordProd_nil, eq_comm, hB.eq_one_iff x hx y hy] at h
    exact ⟨[], trivial, rfl, h, by simp⟩
  | append_singleton ω i ih =>
    have hred := isReduced_of_isReduced_concat hω
    have hmem : cs.wordProd (ω ++ [i]) ∈ cs.parabolic J := h ▸ hB.mem_parabolic x hx y hy
    have hi : i ∈ J := mem_of_isReduced_of_mem_parabolic cs hω hmem (by simp)
    obtain ⟨z, hz, hyz, hxz⟩ := hB.exists_simple x hx y hy i hi
    rw [← h, cs.wordProd_append, cs.wordProd_singleton, mul_assoc, cs.simple_mul_simple_self,
      mul_one] at hxz
    obtain ⟨γ, hγ, htype, hend, hR⟩ := ih hz hred hxz.symm
    refine ⟨γ ++ [(i, y)], ?_, by simp [htype], by simp, ?_⟩
    · rw [isStrictGallery_concat, hend]
      exact ⟨hγ, hB.symm_of_eq_simple hy hz hi hyz⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hR p hp
      · rw [List.mem_singleton.mp hp]; exact hy

theorem dist_eq_simple_of_eq_simple {x y z : C} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) {i : ι}
    (hi : i ∈ J) (hxy : δ x y = cs.simple i) (hzy : δ z y = cs.simple i) (hne : x ≠ z) :
    δ x z = cs.simple i := by
  have hyz := hB.symm_of_eq_simple hz hy hi hzy
  rcases (hB.mul_simple x hx y hy z hz i hi hyz).1 with h | h
  · rwa [h]
  · exfalso
    rw [hxy, cs.simple_mul_simple_self, hB.eq_one_iff x hx z hz] at h
    exact hne h

theorem eq_of_isStrictGallery {x : C} (hx : x ∈ R) {γ γ' : List (ι × C)}
    (hγ : IsStrictGallery cs δ x γ) (hγ' : IsStrictGallery cs δ x γ')
    (hR : ∀ p ∈ γ, p.2 ∈ R) (hR' : ∀ p ∈ γ', p.2 ∈ R) (hJ : ∀ i ∈ galleryType γ, i ∈ J)
    (htype : galleryType γ = galleryType γ') (hred : cs.IsReduced (galleryType γ))
    (hend : galleryEnd x γ = galleryEnd x γ') : γ = γ' := by
  induction γ using List.reverseRecOn generalizing γ' with
  | nil =>
    have : γ' = [] := by
      rw [← List.length_eq_zero_iff, ← length_galleryType, ← htype]
      rfl
    exact this.symm
  | append_singleton γ p ih =>
    obtain rfl | ⟨γ'', p', rfl⟩ := List.eq_nil_or_concat' γ'
    · simp at htype
    rw [galleryType_append, galleryType_append] at htype
    have hlen : (galleryType γ).length = (galleryType γ'').length := by
      have := congrArg List.length htype
      simpa using this
    obtain ⟨ht1, ht2⟩ := List.append_inj htype hlen
    simp only [galleryType_cons, galleryType_nil, List.cons.injEq, and_true] at ht2
    simp only [galleryEnd_concat] at hend
    have hpp' : p = p' := Prod.ext ht2 hend
    subst hpp'
    rw [isStrictGallery_concat] at hγ hγ'
    rw [galleryType_append] at hred
    have hred' := isReduced_of_isReduced_concat hred
    have hRγ : ∀ q ∈ γ, q.2 ∈ R := fun q hq => hR q (by simp [hq])
    have hRγ'' : ∀ q ∈ γ'', q.2 ∈ R := fun q hq => hR' q (by simp [hq])
    have hJ' : ∀ i ∈ galleryType γ, i ∈ J := fun i hi => hJ i (by simp [hi])
    have hJ'' : ∀ i ∈ galleryType γ'', i ∈ J := fun i hi => hJ' i (ht1 ▸ hi)
    have hendR : ∀ η : List (ι × C), (∀ q ∈ η, q.2 ∈ R) → galleryEnd x η ∈ R := by
      intro η hη
      rcases List.eq_nil_or_concat' η with rfl | ⟨η', q, rfl⟩
      · exact hx
      · rw [galleryEnd_concat]; exact hη q (by simp)
    have hz : galleryEnd x γ = galleryEnd x γ'' := by
      by_contra hne
      have h1 := hB.dist_eq hx hγ.1 hRγ hJ' hred'
      have h2 := hB.dist_eq hx hγ'.1 hRγ'' hJ'' (ht1 ▸ hred')
      have hzz := hB.dist_eq_simple_of_eq_simple (hendR γ hRγ) (hR p (by simp))
        (hendR γ'' hRγ'') (hJ p.1 (by simp)) hγ.2 hγ'.2 hne
      have hlen' := length_mul_simple_of_isReduced_concat hred
      rw [← h1] at hlen'
      have h3 := (hB.mul_simple x hx _ (hendR γ hRγ) _ (hendR γ'' hRγ'') p.1 (hJ p.1 (by simp))
        hzz).2 hlen'
      rw [h2, ← ht1, ← h1] at h3
      have h4 := congrArg cs.length h3
      omega
    rw [ih hγ.1 hγ'.1 hRγ hRγ'' hJ' ht1 hred' hz]

end IsBuildingOn

namespace ChamberSystem

variable (X : ChamberSystem ι C) (cs) in
@[expose] def IsResidueBuilding (J : Set ι) (x : C) : Prop :=
  ∃ δ : C → C → W, IsBuildingOn cs δ J (X.residue J x) ∧
    ∀ y ∈ X.residue J x, ∀ z ∈ X.residue J x, ∀ j ∈ J,
      (X.adj j y z ↔ δ y z = 1 ∨ δ y z = cs.simple j)

end ChamberSystem

end CFSG.Monster.B.Geometry
