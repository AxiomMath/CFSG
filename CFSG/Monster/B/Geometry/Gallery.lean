module

public import CFSG.Monster.B.Geometry.Building

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

theorem isReduced_of_isReduced_concat {ω : List ι} {i : ι} (h : cs.IsReduced (ω ++ [i])) :
    cs.IsReduced ω := by
  simpa using h.take ω.length

theorem length_mul_simple_of_isReduced_concat {ω : List ι} {i : ι}
    (h : cs.IsReduced (ω ++ [i])) :
    cs.length (cs.wordProd ω * cs.simple i) = cs.length (cs.wordProd ω) + 1 := by
  have h1 : cs.length (cs.wordProd (ω ++ [i])) = ω.length + 1 := by simpa using h.eq
  rw [cs.wordProd_append, cs.wordProd_singleton] at h1
  rw [h1, (isReduced_of_isReduced_concat h).eq]

theorem mem_parabolic_singleton_iff {i : ι} {w : W} :
    w ∈ cs.parabolic {i} ↔ w = 1 ∨ w = cs.simple i := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨ω, hred, hJ, rfl⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic h
    have hall : ∀ j ∈ ω, j = i := fun j hj => by simpa using hJ j hj
    match ω, hred, hall with
    | [], _, _ => exact Or.inl cs.wordProd_nil
    | [a], _, hall => exact Or.inr (by rw [cs.wordProd_singleton, hall a (by simp)])
    | a :: b :: ω, hred, hall =>
      have hc := hred.isChain_ne
      simp only [List.isChain_cons_cons] at hc
      exact absurd ((hall a (by simp)).trans (hall b (by simp)).symm) hc.1
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact cs.simple_mem_parabolic rfl

section Building

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem IsStrictGallery.dist_eq {x : C} {γ : List (ι × C)} (hγ : IsStrictGallery cs δ x γ)
    (hred : cs.IsReduced (galleryType γ)) :
    δ x (galleryEnd x γ) = cs.wordProd (galleryType γ) := by
  induction γ using List.reverseRecOn with
  | nil => simp [hδ.eq_one_self]
  | append_singleton γ p ih =>
    rw [isStrictGallery_concat] at hγ
    rw [galleryType_append] at hred
    have hred' := isReduced_of_isReduced_concat hred
    have h := ih hγ.1 hred'
    have hlen := length_mul_simple_of_isReduced_concat hred
    rw [← h] at hlen
    rw [galleryEnd_concat, (hδ.mul_simple x _ p.2 p.1 hγ.2).2 hlen, h, galleryType_append,
      cs.wordProd_append]
    simp [galleryType]

theorem IsStrictGallery.dist_take {x : C} {γ : List (ι × C)} (hγ : IsStrictGallery cs δ x γ)
    (hred : cs.IsReduced (galleryType γ)) (k : ℕ) :
    δ x (galleryEnd x (γ.take k)) = cs.wordProd ((galleryType γ).take k) := by
  have hγ' : IsStrictGallery cs δ x (γ.take k) := by
    have := (isStrictGallery_append (cs := cs) (δ := δ) x (γ.take k) (γ.drop k)).mp
      (by rwa [List.take_append_drop])
    exact this.1
  have ht : galleryType (γ.take k) = (galleryType γ).take k := List.map_take ..
  rw [hγ'.dist_eq hδ (by rw [ht]; exact hred.take k), ht]

theorem exists_strictGallery {x y : C} {ω : List ι} (hω : cs.IsReduced ω)
    (h : cs.wordProd ω = δ x y) :
    ∃ γ : List (ι × C), IsStrictGallery cs δ x γ ∧ galleryType γ = ω ∧ galleryEnd x γ = y := by
  induction ω using List.reverseRecOn generalizing y with
  | nil =>
    rw [cs.wordProd_nil, eq_comm, hδ.eq_one_iff] at h
    exact ⟨[], trivial, rfl, h⟩
  | append_singleton ω i ih =>
    have hred := isReduced_of_isReduced_concat hω
    obtain ⟨z, hyz, hxz⟩ := hδ.exists_simple x y i
    rw [← h, cs.wordProd_append, cs.wordProd_singleton, mul_assoc, cs.simple_mul_simple_self,
      mul_one] at hxz
    obtain ⟨γ, hγ, htype, hend⟩ := ih hred hxz.symm
    refine ⟨γ ++ [(i, y)], ?_, by simp [htype], by simp⟩
    rw [isStrictGallery_concat, hend]
    exact ⟨hγ, hδ.symm_of_eq_simple hyz⟩

theorem dist_inv (x y : C) : δ y x = (δ x y)⁻¹ := by
  obtain ⟨ω, hω, hprod⟩ := cs.exists_isReduced (δ x y)
  obtain ⟨γ, hγ, htype, rfl⟩ := exists_strictGallery hδ hω hprod.symm
  have hrev := hγ.reverse hδ
  have hred : cs.IsReduced (galleryType (galleryReverse x γ)) := by
    rw [galleryType_galleryReverse, htype]
    exact hω.reverse
  have := hrev.dist_eq hδ hred
  rw [galleryEnd_galleryReverse, galleryType_galleryReverse, htype, cs.wordProd_reverse] at this
  rw [this, hprod]

theorem dist_eq_simple_of_eq_simple {x y z : C} {i : ι} (hxy : δ x y = cs.simple i)
    (hzy : δ z y = cs.simple i) (hne : x ≠ z) : δ x z = cs.simple i := by
  have hyz := hδ.symm_of_eq_simple hzy
  rcases (hδ.mul_simple x y z i hyz).1 with h | h
  · rwa [h]
  · exfalso
    rw [hxy, cs.simple_mul_simple_self, hδ.eq_one_iff] at h
    exact hne h

theorem eq_of_isStrictGallery {x : C} {γ γ' : List (ι × C)} (hγ : IsStrictGallery cs δ x γ)
    (hγ' : IsStrictGallery cs δ x γ') (htype : galleryType γ = galleryType γ')
    (hred : cs.IsReduced (galleryType γ)) (hend : galleryEnd x γ = galleryEnd x γ') :
    γ = γ' := by
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
    have hz : galleryEnd x γ = galleryEnd x γ'' := by
      by_contra hne
      have h1 := hγ.1.dist_eq hδ hred'
      have h2 := hγ'.1.dist_eq hδ (ht1 ▸ hred')
      have hzz := dist_eq_simple_of_eq_simple hδ hγ.2 hγ'.2 hne
      have hlen' := length_mul_simple_of_isReduced_concat hred
      rw [← h1] at hlen'
      have h3 := (hδ.mul_simple x _ _ p.1 hzz).2 hlen'
      rw [h2, ← ht1, ← h1] at h3
      have h4 := congrArg cs.length h3
      omega
    rw [ih hγ.1 hγ'.1 ht1 hred' hz]

theorem mem_residue_iff_mem_parabolic {J : Set ι} {x y : C} :
    y ∈ residue cs δ J x ↔ δ x y ∈ cs.parabolic J := by
  refine ⟨fun h => mem_parabolic_of_mem_residue hδ (self_mem_residue J x) h, fun h => ?_⟩
  obtain ⟨ω, hω, hprod⟩ := cs.exists_isReduced (δ x y)
  obtain ⟨γ, hγ, htype, hend⟩ := exists_strictGallery hδ hω hprod.symm
  refine mem_residue_iff.mpr ⟨γ, hγ, fun i hi => ?_, hend⟩
  rw [htype] at hi
  exact mem_of_isReduced_of_mem_parabolic cs hω (hprod ▸ h) hi

theorem mem_panel_iff {i : ι} {x y : C} :
    y ∈ panel cs δ i x ↔ δ x y = 1 ∨ δ x y = cs.simple i := by
  rw [panel, mem_residue_iff_mem_parabolic hδ, mem_parabolic_singleton_iff]

theorem residue_inter (J K : Set ι) (x : C) :
    residue cs δ J x ∩ residue cs δ K x = residue cs δ (J ∩ K) x := by
  ext y
  simp only [Set.mem_inter_iff, mem_residue_iff_mem_parabolic hδ, ← parabolic_inter cs J K,
    Subgroup.mem_inf]

theorem residue_univ (x : C) : residue cs δ Set.univ x = Set.univ := by
  ext y
  simp [mem_residue_iff_mem_parabolic hδ, cs.parabolic_univ]

@[expose] def galleryMap {C' : Type*} (f : C → C') (γ : List (ι × C)) : List (ι × C') :=
  γ.map fun p => (p.1, f p.2)

omit hδ in
@[simp] theorem galleryType_galleryMap {C' : Type*} (f : C → C') (γ : List (ι × C)) :
    galleryType (galleryMap f γ) = galleryType γ := by
  simp [galleryMap, galleryType]

omit hδ in
theorem galleryEnd_galleryMap {C' : Type*} (f : C → C') (x : C) (γ : List (ι × C)) :
    galleryEnd (f x) (galleryMap f γ) = f (galleryEnd x γ) := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih => exact ih p.2

omit hδ in
theorem IsStrictGallery.mem_residue {J : Set ι} {x : C} {γ : List (ι × C)}
    (hγ : IsStrictGallery cs δ x γ) (hJ : ∀ i ∈ galleryType γ, i ∈ J) :
    ∀ p ∈ γ, p.2 ∈ residue cs δ J x := by
  induction γ generalizing x with
  | nil => simp
  | cons q γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    have hq : q.2 ∈ residue cs δ J x :=
      Relation.ReflTransGen.single ⟨q.1, hJ q.1 (by simp), h1⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hq
    · exact mem_residue_trans hq (ih h2 (fun i hi => hJ i (by simp [hi])) p hp)

omit hδ in
theorem IsStrictGallery.map {C' : Type*} {δ' : C' → C' → W} {X : Set C} {f : C → C'}
    (hf : ∀ y ∈ X, ∀ z ∈ X, ∀ i, δ y z = cs.simple i → δ' (f y) (f z) = cs.simple i)
    {x : C} (hx : x ∈ X) {γ : List (ι × C)} (hγ : IsStrictGallery cs δ x γ)
    (hX : ∀ p ∈ γ, p.2 ∈ X) : IsStrictGallery cs δ' (f x) (galleryMap f γ) := by
  induction γ generalizing x with
  | nil => trivial
  | cons q γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    have hq : q.2 ∈ X := hX q (by simp)
    exact ⟨hf x hx q.2 hq q.1 h1, ih hq h2 fun p hp => hX p (by simp [hp])⟩

theorem dist_map_eq {C' : Type*} {δ' : C' → C' → W} (hδ' : IsWeylDistanceBuilding cs δ')
    {J : Set ι} {a : C} {f : C → C'}
    (hf : ∀ y ∈ residue cs δ J a, ∀ z ∈ residue cs δ J a, ∀ i,
      δ y z = cs.simple i → δ' (f y) (f z) = cs.simple i)
    {x y : C} (hx : x ∈ residue cs δ J a) (hy : y ∈ residue cs δ J a) :
    δ' (f x) (f y) = δ x y := by
  have hxy : δ x y ∈ cs.parabolic J := mem_parabolic_of_mem_residue hδ hx hy
  obtain ⟨ω, hω, hprod⟩ := cs.exists_isReduced (δ x y)
  obtain ⟨γ, hγ, htype, rfl⟩ := exists_strictGallery hδ hω hprod.symm
  have hJ : ∀ i ∈ galleryType γ, i ∈ J := fun i hi =>
    mem_of_isReduced_of_mem_parabolic cs hω (hprod ▸ hxy) (htype ▸ hi)
  have hX : ∀ p ∈ γ, p.2 ∈ residue cs δ J a := fun p hp => by
    rw [← residue_eq_of_mem hδ hx]
    exact hγ.mem_residue hJ p hp
  have hγ' := hγ.map hf hx hX
  have := hγ'.dist_eq hδ' (by rw [galleryType_galleryMap, htype]; exact hω)
  rw [galleryEnd_galleryMap, galleryType_galleryMap, htype] at this
  rw [this, hprod]

theorem IsTypeIso.dist_eq {C' : Type*} {δ' : C' → C' → W} (hδ' : IsWeylDistanceBuilding cs δ')
    {J : Set ι} {a : C} {X' : Set C'} {f : C → C'}
    (hf : IsTypeIso cs δ δ' (residue cs δ J a) X' f) {x y : C}
    (hx : x ∈ residue cs δ J a) (hy : y ∈ residue cs δ J a) : δ' (f x) (f y) = δ x y :=
  dist_map_eq hδ hδ' (fun y hy z hz i h => (hf.2 y hy z hz i).mpr h) hx hy

theorem IsTypeIso.isWeylIsometry {C' : Type*} {δ' : C' → C' → W}
    (hδ' : IsWeylDistanceBuilding cs δ') {J : Set ι} {a : C} {X' : Set C'} {f : C → C'}
    (hf : IsTypeIso cs δ δ' (residue cs δ J a) X' f) :
    IsWeylIsometry δ δ' (residue cs δ J a) X' f :=
  ⟨hf.1, fun _ hx _ hy => hf.dist_eq hδ hδ' hx hy⟩

theorem dist_typeAut {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) (x y : C) :
    δ (g x) (g y) = δ x y := by
  exact dist_map_eq hδ hδ (J := Set.univ) (a := x) (f := g) (x := x) (y := y)
    (fun y _ z _ i h => (hg y z i).mpr h) (self_mem_residue _ x)
    (by rw [residue_univ hδ]; trivial)

end Building

end CFSG.Monster.B.Geometry
