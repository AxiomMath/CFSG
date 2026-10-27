module

public import CFSG.Monster.B.Geometry.Gallery

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

theorem galleryType_eq_append_iff {γ : List (ι × C)} {ω₁ ω₂ : List ι} :
    galleryType γ = ω₁ ++ ω₂ ↔
      ∃ γ₁ γ₂, γ = γ₁ ++ γ₂ ∧ galleryType γ₁ = ω₁ ∧ galleryType γ₂ = ω₂ := by
  unfold galleryType
  rw [List.map_eq_append_iff]

section Building

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem dist_eq_mul_of_length_add {x y z : C}
    (h : cs.length (δ x y * δ y z) = cs.length (δ x y) + cs.length (δ y z)) :
    δ x z = δ x y * δ y z := by
  obtain ⟨α, hα, hαp⟩ := cs.exists_isReduced (δ x y)
  obtain ⟨β, hβ, hβp⟩ := cs.exists_isReduced (δ y z)
  obtain ⟨γ₁, hγ₁, ht₁, he₁⟩ := exists_strictGallery hδ hα hαp.symm
  obtain ⟨γ₂, hγ₂, ht₂, he₂⟩ := exists_strictGallery hδ hβ hβp.symm
  have hcat : IsStrictGallery cs δ x (γ₁ ++ γ₂) :=
    (isStrictGallery_append x γ₁ γ₂).mpr ⟨hγ₁, he₁ ▸ hγ₂⟩
  have hred : cs.IsReduced (galleryType (γ₁ ++ γ₂)) := by
    rw [galleryType_append, ht₁, ht₂, CoxeterSystem.IsReduced, cs.wordProd_append, ← hαp, ← hβp,
      h, List.length_append, ← hα.eq, ← hβ.eq, ← hαp, ← hβp]
  have := hcat.dist_eq hδ hred
  rw [galleryEnd_append, he₁, he₂, galleryType_append, ht₁, ht₂, cs.wordProd_append, ← hαp,
    ← hβp] at this
  exact this

theorem gate_of_isMinimalCosetRep {J : Set ι} {y z p : C} (hp : p ∈ residue cs δ J y)
    (hmin : cs.IsMinimalCosetRep J (δ z p)) {q : C} (hq : q ∈ residue cs δ J y) :
    δ z q = δ z p * δ p q ∧ cs.length (δ z q) = cs.length (δ z p) + cs.length (δ p q) := by
  have hpq : δ p q ∈ cs.parabolic J := mem_parabolic_of_mem_residue hδ hp hq
  have hlen := cs.length_mul_of_isMinimalCosetRep hmin hpq
  have h := dist_eq_mul_of_length_add hδ hlen
  exact ⟨h, by rw [h, hlen]⟩

theorem isMinimalCosetRep_of_forall_le {J : Set ι} {y z p : C} (hp : p ∈ residue cs δ J y)
    (hle : ∀ q ∈ residue cs δ J y, cs.length (δ z p) ≤ cs.length (δ z q)) :
    cs.IsMinimalCosetRep J (δ z p) := by
  rw [cs.isMinimalCosetRep_iff]
  intro i hi hdesc
  obtain ⟨q, hpq, hzq⟩ := hδ.exists_simple z p i
  have hq : q ∈ residue cs δ J y :=
    mem_residue_trans hp (Relation.ReflTransGen.single ⟨i, hi, hpq⟩)
  have := hle q hq
  rw [hzq] at this
  exact absurd hdesc (not_lt.mpr this)

theorem exists_gate (J : Set ι) (y z : C) :
    ∃ p ∈ residue cs δ J y, ∀ q ∈ residue cs δ J y,
      δ z q = δ z p * δ p q ∧ cs.length (δ z q) = cs.length (δ z p) + cs.length (δ p q) := by
  classical
  have hex : ∃ n, ∃ q ∈ residue cs δ J y, cs.length (δ z q) = n :=
    ⟨_, y, self_mem_residue J y, rfl⟩
  obtain ⟨p, hp, hpn⟩ := Nat.find_spec hex
  have hle : ∀ q ∈ residue cs δ J y, cs.length (δ z p) ≤ cs.length (δ z q) := fun q hq => by
    rw [hpn]
    exact Nat.find_min' hex ⟨q, hq, rfl⟩
  exact ⟨p, hp, fun q hq => gate_of_isMinimalCosetRep hδ hp
    (isMinimalCosetRep_of_forall_le hδ hp hle) hq⟩

theorem isProjection_of_gate {J : Set ι} {y z p : C} (hp : p ∈ residue cs δ J y)
    (hgate : ∀ q ∈ residue cs δ J y,
      cs.length (δ z q) = cs.length (δ z p) + cs.length (δ p q)) :
    IsProjection cs δ (residue cs δ J y) z p := by
  refine ⟨hp, fun q hq hne => ?_⟩
  have h1 := hgate q hq
  have h2 : cs.length (δ p q) ≠ 0 := by
    rw [Ne, cs.length_eq_zero_iff, hδ.eq_one_iff]
    exact fun h => hne h.symm
  omega

theorem exists_isProjection (J : Set ι) (y z : C) :
    ∃ p, IsProjection cs δ (residue cs δ J y) z p := by
  obtain ⟨p, hp, hgate⟩ := exists_gate hδ J y z
  exact ⟨p, isProjection_of_gate hδ hp fun q hq => (hgate q hq).2⟩

omit hδ in
theorem IsProjection.unique {R : Set C} {z p p' : C} (hp : IsProjection cs δ R z p)
    (hp' : IsProjection cs δ R z p') : p = p' := by
  by_contra hne
  have h1 := hp.2 p' hp'.1 (Ne.symm hne)
  have h2 := hp'.2 p hp.1 hne
  omega

theorem IsProjection.gate {J : Set ι} {y z p : C} (hp : IsProjection cs δ (residue cs δ J y) z p)
    {q : C} (hq : q ∈ residue cs δ J y) :
    δ z q = δ z p * δ p q ∧ cs.length (δ z q) = cs.length (δ z p) + cs.length (δ p q) := by
  refine gate_of_isMinimalCosetRep hδ hp.1 (isMinimalCosetRep_of_forall_le hδ hp.1 ?_) hq
  intro q hq
  by_cases h : q = p
  · rw [h]
  · exact (hp.2 q hq h).le

theorem mem_residue_of_dist_mul {J : Set ι} {a x y c : C} (hx : x ∈ residue cs δ J a)
    (hy : y ∈ residue cs δ J a) (hmul : δ x y = δ x c * δ c y)
    (hlen : cs.length (δ x y) = cs.length (δ x c) + cs.length (δ c y)) :
    c ∈ residue cs δ J a := by
  have hxy : δ x y ∈ cs.parabolic J := mem_parabolic_of_mem_residue hδ hx hy
  obtain ⟨α, hα, hαp⟩ := cs.exists_isReduced (δ x c)
  obtain ⟨β, hβ, hβp⟩ := cs.exists_isReduced (δ c y)
  have hred : cs.IsReduced (α ++ β) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, ← hαp, ← hβp, ← hmul, hlen,
      List.length_append, ← hα.eq, ← hβ.eq, ← hαp, ← hβp]
  have hmem : cs.wordProd (α ++ β) ∈ cs.parabolic J := by
    rw [cs.wordProd_append, ← hαp, ← hβp, ← hmul]
    exact hxy
  have hc : δ x c ∈ cs.parabolic J := by
    rw [hαp]
    exact cs.wordProd_mem_parabolic fun i hi =>
      mem_of_isReduced_of_mem_parabolic cs hred hmem (List.mem_append_left β hi)
  rw [← residue_eq_of_mem hδ hx]
  exact (mem_residue_iff_mem_parabolic hδ).mpr hc

theorem IsProjection.mem_residue_of_mem {J K : Set ι} {x v p : C}
    (hp : IsProjection cs δ (residue cs δ J x) v p) (hv : v ∈ residue cs δ K x) :
    p ∈ residue cs δ K x := by
  obtain ⟨hmul, hlen⟩ := hp.gate hδ (self_mem_residue J x)
  exact mem_residue_of_dist_mul hδ hv (self_mem_residue K x) hmul hlen

omit hδ in
theorem IsProjection.map {C' : Type*} {δ' : C' → C' → W} {R : Set C} {R' : Set C'} {z p : C}
    {f : C → C'} (hp : IsProjection cs δ R z p) (hf : Set.BijOn f R R')
    (hd : ∀ q ∈ R, δ' (f z) (f q) = δ z q) : IsProjection cs δ' R' (f z) (f p) := by
  refine ⟨hf.mapsTo hp.1, fun q' hq' hne => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hf.surjOn hq'
  have hqp : q ≠ p := fun h => hne (h ▸ rfl)
  rw [hd p hp.1, hd q hq]
  exact hp.2 q hq hqp

theorem exists_dist_eq_of_length_add {x y : C} {u w : W} (hxy : δ x y = w)
    (hlen : cs.length (u⁻¹ * w) + cs.length u = cs.length w) :
    ∃ c, δ x c = u ∧ δ c y = u⁻¹ * w := by
  obtain ⟨α, hα, hαp⟩ := cs.exists_isReduced u
  obtain ⟨β, hβ, hβp⟩ := cs.exists_isReduced (u⁻¹ * w)
  have hred : cs.IsReduced (α ++ β) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, ← hαp, ← hβp, mul_inv_cancel_left,
      List.length_append, ← hα.eq, ← hβ.eq, ← hαp, ← hβp, ← hlen, add_comm]
  have hprod : cs.wordProd (α ++ β) = δ x y := by
    rw [cs.wordProd_append, ← hαp, ← hβp, mul_inv_cancel_left, hxy]
  obtain ⟨γ, hγ, htype, hend⟩ := exists_strictGallery hδ hred hprod
  obtain ⟨γ₁, γ₂, hγ12, ht₁, ht₂⟩ := galleryType_eq_append_iff.mp htype
  subst hγ12
  rw [isStrictGallery_append] at hγ
  refine ⟨galleryEnd x γ₁, ?_, ?_⟩
  · rw [hγ.1.dist_eq hδ (ht₁ ▸ hα), ht₁, hαp]
  · have h := hγ.2.dist_eq hδ (ht₂ ▸ hβ)
    rw [← galleryEnd_append, hend, ht₂, ← hβp] at h
    exact h

theorem eq_of_dist_eq_of_length_add {x y c c' : C} {u w : W}
    (hlen : cs.length (u⁻¹ * w) + cs.length u = cs.length w) (hc : δ x c = u)
    (hcy : δ c y = u⁻¹ * w) (hc' : δ x c' = u) (hc'y : δ c' y = u⁻¹ * w) : c = c' := by
  obtain ⟨α, hα, hαp⟩ := cs.exists_isReduced u
  obtain ⟨β, hβ, hβp⟩ := cs.exists_isReduced (u⁻¹ * w)
  have hred : cs.IsReduced (α ++ β) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, ← hαp, ← hβp, mul_inv_cancel_left,
      List.length_append, ← hα.eq, ← hβ.eq, ← hαp, ← hβp, ← hlen, add_comm]
  have key : ∀ e : C, δ x e = u → δ e y = u⁻¹ * w →
      ∃ γ₁ γ₂ : List (ι × C), IsStrictGallery cs δ x (γ₁ ++ γ₂) ∧
        galleryType γ₁ = α ∧ galleryType γ₂ = β ∧ galleryEnd x γ₁ = e ∧
        galleryEnd x (γ₁ ++ γ₂) = y := by
    intro e he hey
    obtain ⟨γ₁, hγ₁, ht₁, he₁⟩ := exists_strictGallery hδ hα (hαp.symm.trans he.symm)
    obtain ⟨γ₂, hγ₂, ht₂, he₂⟩ := exists_strictGallery hδ hβ (hβp.symm.trans hey.symm)
    refine ⟨γ₁, γ₂, (isStrictGallery_append x γ₁ γ₂).mpr ⟨hγ₁, he₁ ▸ hγ₂⟩, ht₁, ht₂, he₁, ?_⟩
    rw [galleryEnd_append, he₁, he₂]
  obtain ⟨γ₁, γ₂, hγ, ht₁, ht₂, he₁, he⟩ := key c hc hcy
  obtain ⟨η₁, η₂, hη, hs₁, hs₂, hf₁, hf⟩ := key c' hc' hc'y
  have heq := eq_of_isStrictGallery hδ hγ hη (by rw [galleryType_append, galleryType_append,
    ht₁, ht₂, hs₁, hs₂]) (by rw [galleryType_append, ht₁, ht₂]; exact hred) (he.trans hf.symm)
  have hl : γ₁.length = η₁.length := by
    rw [← length_galleryType, ← length_galleryType, ht₁, hs₁]
  obtain ⟨rfl, -⟩ := List.append_inj heq hl
  rw [← he₁, ← hf₁]

section Spherical

variable [Finite W]

omit hδ in
theorem isLongest_univ : IsLongest cs Set.univ (longest cs Set.univ) :=
  isLongest_longest Set.univ

omit hδ in
theorem isLongest_of_finite (J : Set ι) : IsLongest cs J (longest cs J) :=
  isLongest_longest J

omit hδ in
theorem length_inv_mul_longest (u : W) :
    cs.length (u⁻¹ * longest cs Set.univ) + cs.length u = cs.length (longest cs Set.univ) :=
  isLongest_univ.length_inv_mul (by rw [cs.parabolic_univ]; trivial)

omit hδ in
theorem longest_singleton (i : ι) : longest cs {i} = cs.simple i := by
  have h := isLongest_of_finite (cs := cs) {i}
  rcases mem_parabolic_singleton_iff.mp h.1 with h1 | h1
  · have := h.2 _ (cs.simple_mem_parabolic (Set.mem_singleton i))
    rw [h1, cs.length_one, cs.length_simple] at this
    omega
  · exact h1

open _root_.Classical in
variable (cs δ) in
@[expose] noncomputable def oppChamber (x d : C) (u : W) : C :=
  if h : ∃ c, δ x c = u ∧ δ c d = u⁻¹ * longest cs Set.univ then h.choose else x

theorem exists_oppChamber {x d : C} (hxd : δ x d = longest cs Set.univ) (u : W) :
    ∃ c, δ x c = u ∧ δ c d = u⁻¹ * longest cs Set.univ :=
  exists_dist_eq_of_length_add hδ hxd (length_inv_mul_longest u)

theorem oppChamber_spec {x d : C} (hxd : δ x d = longest cs Set.univ) (u : W) :
    δ x (oppChamber cs δ x d u) = u ∧ δ (oppChamber cs δ x d u) d = u⁻¹ * longest cs Set.univ := by
  have h := exists_oppChamber hδ hxd u
  rw [oppChamber, dite_eq_left h]
  exact h.choose_spec

theorem eq_oppChamber {x d c : C} (hxd : δ x d = longest cs Set.univ) {u : W}
    (hc : δ x c = u) (hcd : δ c d = u⁻¹ * longest cs Set.univ) : c = oppChamber cs δ x d u :=
  eq_of_dist_eq_of_length_add hδ (length_inv_mul_longest u) hc hcd
    (oppChamber_spec hδ hxd u).1 (oppChamber_spec hδ hxd u).2

theorem oppChamber_one {x d : C} (hxd : δ x d = longest cs Set.univ) :
    oppChamber cs δ x d 1 = x :=
  (eq_oppChamber hδ hxd (hδ.eq_one_self x) (by rw [inv_one, one_mul, hxd])).symm

theorem oppChamber_longest {x d : C} (hxd : δ x d = longest cs Set.univ) :
    oppChamber cs δ x d (longest cs Set.univ) = d :=
  (eq_oppChamber hδ hxd hxd (by rw [inv_mul_cancel, hδ.eq_one_self])).symm

theorem dist_oppChamber_mul_simple {x d : C} (hxd : δ x d = longest cs Set.univ) {u : W}
    {i : ι} (hu : cs.length (u * cs.simple i) = cs.length u + 1) :
    δ (oppChamber cs δ x d u) (oppChamber cs δ x d (u * cs.simple i)) = cs.simple i := by
  obtain ⟨α, hα, hαp⟩ := cs.exists_isReduced u
  obtain ⟨β, hβ, hβp⟩ := cs.exists_isReduced ((u * cs.simple i)⁻¹ * longest cs Set.univ)
  have hlen := length_inv_mul_longest (cs := cs) (u * cs.simple i)
  have hred : cs.IsReduced (α ++ [i] ++ β) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, cs.wordProd_append, cs.wordProd_singleton,
      ← hαp, ← hβp, mul_inv_cancel_left, List.length_append, List.length_append,
      List.length_singleton, ← hα.eq, ← hβ.eq, ← hαp, ← hβp, ← hlen, hu]
    omega
  have hprod : cs.wordProd (α ++ [i] ++ β) = δ x d := by
    rw [cs.wordProd_append, cs.wordProd_append, cs.wordProd_singleton, ← hαp, ← hβp,
      mul_inv_cancel_left, hxd]
  obtain ⟨γ, hγ, htype, hend⟩ := exists_strictGallery hδ hred hprod
  obtain ⟨γ₀, γ₂, hγ02, ht₀, ht₂⟩ := galleryType_eq_append_iff.mp htype
  obtain ⟨γ₁, γ₃, hγ13, ht₁, ht₃⟩ := galleryType_eq_append_iff.mp ht₀
  obtain ⟨p, hp3⟩ : ∃ p, γ₃ = [p] := by
    have : γ₃.length = 1 := by rw [← length_galleryType, ht₃]; rfl
    exact List.length_eq_one_iff.mp this
  subst hγ02 hγ13 hp3
  have hpi : p.1 = i := by simpa [galleryType] using ht₃
  have hs := hγ
  rw [isStrictGallery_append, isStrictGallery_append] at hs
  have hendp : galleryEnd x (γ₁ ++ [p]) = p.2 := galleryEnd_concat x γ₁ p
  have hend₂ : galleryEnd p.2 γ₂ = d := by
    rw [← hendp, ← galleryEnd_append]
    exact hend
  have hred₁ : cs.IsReduced (α ++ [i]) := by
    have := hred.take (α ++ [i]).length
    rwa [List.take_left] at this
  have hred₂ : cs.IsReduced ([i] ++ β) := by
    have := hred.drop α.length
    rwa [List.append_assoc, List.drop_left] at this
  have hc₁ : galleryEnd x γ₁ = oppChamber cs δ x d u := by
    refine eq_oppChamber hδ hxd ?_ ?_
    · rw [hs.1.1.dist_eq hδ (ht₁ ▸ hα), ht₁, hαp]
    · have hg : IsStrictGallery cs δ (galleryEnd x γ₁) (p :: γ₂) :=
        ⟨by simpa using hs.1.2, by rw [← hendp]; exact hs.2⟩
      have ht : galleryType (p :: γ₂) = [i] ++ β := by
        rw [galleryType_cons, hpi, ht₂]
        rfl
      have h := hg.dist_eq hδ (ht ▸ hred₂)
      rw [galleryEnd_cons, hend₂, ht, cs.wordProd_append, cs.wordProd_singleton, ← hβp,
        mul_inv_rev, ← mul_assoc, ← mul_assoc, cs.inv_simple, cs.simple_mul_simple_self,
        one_mul] at h
      exact h
  have hc₂ : p.2 = oppChamber cs δ x d (u * cs.simple i) := by
    refine eq_oppChamber hδ hxd ?_ ?_
    · have hg : IsStrictGallery cs δ x (γ₁ ++ [p]) :=
        (isStrictGallery_append _ _ _).mpr hs.1
      have ht : galleryType (γ₁ ++ [p]) = α ++ [i] := by
        rw [galleryType_append, ht₁, ht₃]
      have h := hg.dist_eq hδ (ht ▸ hred₁)
      rw [hendp, ht, cs.wordProd_append, cs.wordProd_singleton, ← hαp] at h
      exact h
    · have h := hs.2.dist_eq hδ (ht₂ ▸ hβ)
      rw [hendp, hend₂, ht₂, ← hβp] at h
      exact h
  have hstep : δ (galleryEnd x γ₁) p.2 = cs.simple p.1 := by
    simpa using hs.1.2
  rw [← hc₁, ← hc₂, hstep, hpi]

theorem dist_oppChamber_mul_simple' {x d : C} (hxd : δ x d = longest cs Set.univ) (u : W)
    (i : ι) : δ (oppChamber cs δ x d u) (oppChamber cs δ x d (u * cs.simple i)) = cs.simple i := by
  rcases cs.length_mul_simple u i with h | h
  · exact dist_oppChamber_mul_simple hδ hxd h
  · have h' : cs.length (u * cs.simple i * cs.simple i) = cs.length (u * cs.simple i) + 1 := by
      rw [mul_assoc, cs.simple_mul_simple_self, mul_one]
      omega
    have := dist_oppChamber_mul_simple hδ hxd h'
    rw [mul_assoc, cs.simple_mul_simple_self, mul_one] at this
    exact hδ.symm_of_eq_simple this

theorem isApartmentMap_oppChamber {x d : C} (hxd : δ x d = longest cs Set.univ) :
    IsApartmentMap δ (oppChamber cs δ x d) := by
  intro u v
  suffices h : ∀ ω : List ι, cs.IsReduced ω →
      δ (oppChamber cs δ x d u) (oppChamber cs δ x d (u * cs.wordProd ω)) = cs.wordProd ω by
    obtain ⟨ω, hω, hωp⟩ := cs.exists_isReduced (u⁻¹ * v)
    have := h ω hω
    rwa [← hωp, mul_inv_cancel_left] at this
  intro ω hω
  induction ω using List.reverseRecOn with
  | nil => simp [hδ.eq_one_self]
  | append_singleton ω i ih =>
    have hred := isReduced_of_isReduced_concat hω
    have h1 := ih hred
    have hlen := length_mul_simple_of_isReduced_concat hω
    rw [← h1] at hlen
    have hstep := dist_oppChamber_mul_simple' hδ hxd (u * cs.wordProd ω) i
    have := (hδ.mul_simple _ _ _ i hstep).2 hlen
    rw [h1] at this
    rwa [cs.wordProd_append, cs.wordProd_singleton, ← mul_assoc]

theorem oppChamber_injective {x d : C} (hxd : δ x d = longest cs Set.univ) :
    Function.Injective (oppChamber cs δ x d) := by
  intro u v h
  have := isApartmentMap_oppChamber hδ hxd u v
  rw [h, hδ.eq_one_self, eq_comm, inv_mul_eq_one] at this
  exact this

theorem isApartment_range_oppChamber {x d : C} (hxd : δ x d = longest cs Set.univ) :
    IsApartment δ (Set.range (oppChamber cs δ x d)) :=
  ⟨_, oppChamber_injective hδ hxd, rfl, isApartmentMap_oppChamber hδ hxd⟩

theorem range_eq_of_isApartmentMap {x d : C} (hxd : δ x d = longest cs Set.univ) {b : W → C}
    (hb : IsApartmentMap δ b) (hx : x ∈ Set.range b) (hd : d ∈ Set.range b) :
    Set.range b = Set.range (oppChamber cs δ x d) := by
  obtain ⟨u₀, rfl⟩ := hx
  obtain ⟨u₁, rfl⟩ := hd
  have h01 : u₀⁻¹ * u₁ = longest cs Set.univ := by rw [← hb, hxd]
  have key : ∀ v, b (u₀ * v) = oppChamber cs δ (b u₀) (b u₁) v := fun v =>
    eq_oppChamber hδ hxd (by rw [hb, inv_mul_cancel_left]) (by
      rw [hb, mul_inv_rev, mul_assoc, h01])
  ext c
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u₀⁻¹ * u, by rw [← key, mul_inv_cancel_left]⟩
  · rintro ⟨v, rfl⟩
    exact ⟨u₀ * v, key v⟩

theorem eq_oppChamber_of_mem {x d c : C} (hxd : δ x d = longest cs Set.univ)
    (hc : c ∈ Set.range (oppChamber cs δ x d)) : c = oppChamber cs δ x d (δ x c) := by
  obtain ⟨u, rfl⟩ := hc
  rw [(oppChamber_spec hδ hxd u).1]

theorem isProjection_oppChamber_longest {x d : C} (hxd : δ x d = longest cs Set.univ)
    (J : Set ι) :
    IsProjection cs δ (residue cs δ J x) d (oppChamber cs δ x d (longest cs J)) := by
  set p := oppChamber cs δ x d (longest cs J)
  obtain ⟨hxp, hpd⟩ := oppChamber_spec hδ hxd (longest cs J)
  have hJ := isLongest_of_finite (cs := cs) J
  have hp : p ∈ residue cs δ J x := (mem_residue_iff_mem_parabolic hδ).mpr (hxp ▸ hJ.1)
  obtain ⟨p', hp'⟩ := exists_isProjection hδ J x d
  suffices h : p' = p from h ▸ hp'
  obtain ⟨-, hlx⟩ := hp'.gate hδ (self_mem_residue J x)
  obtain ⟨-, hlp⟩ := hp'.gate hδ hp
  have hdx : δ d x = longest cs Set.univ := by
    rw [dist_inv hδ, hxd, isLongest_univ.inv_eq]
  have hdp : δ d p = longest cs Set.univ * longest cs J := by
    rw [dist_inv hδ, hpd, mul_inv_rev, inv_inv, isLongest_univ.inv_eq]
  have hle : cs.length (δ p' x) ≤ cs.length (longest cs J) :=
    hJ.2 _ (mem_parabolic_of_mem_residue hδ hp'.1 (self_mem_residue J x))
  have hl0 := isLongest_univ.length_mul (cs := cs) (x := longest cs J)
    (by rw [cs.parabolic_univ]; trivial)
  rw [hdx] at hlx
  rw [hdp] at hlp
  have h0 : cs.length (δ p' p) = 0 := by omega
  rw [cs.length_eq_zero_iff, hδ.eq_one_iff] at h0
  exact h0

theorem dist_eq_longest_of_mem_panel {x d y : C} (hxd : δ x d = longest cs Set.univ) {i : ι}
    (hy : y ∈ panel cs δ i x) (hne : y ≠ oppChamber cs δ x d (cs.simple i)) :
    δ y d = longest cs Set.univ := by
  have hp := isProjection_oppChamber_longest hδ hxd {i}
  rw [longest_singleton] at hp
  set p := oppChamber cs δ x d (cs.simple i)
  obtain ⟨hmul, -⟩ := hp.gate hδ hy
  have hpy : δ p y = cs.simple i := by
    have hpx := (mem_panel_iff hδ).mp hp.1
    have hyx := (mem_panel_iff hδ).mp hy
    have hpy' : y ∈ panel cs δ i p := by
      rw [panel, residue_eq_of_mem hδ hp.1]
      exact hy
    rcases (mem_panel_iff hδ).mp hpy' with h | h
    · exact absurd ((hδ.eq_one_iff p y).mp h).symm hne
    · exact h
  have hdp : δ d p = longest cs Set.univ * cs.simple i := by
    rw [dist_inv hδ, (oppChamber_spec hδ hxd (cs.simple i)).2, mul_inv_rev, inv_inv,
      isLongest_univ.inv_eq]
  rw [dist_inv hδ, hmul, hdp, hpy, mul_assoc, cs.simple_mul_simple_self, mul_one,
    isLongest_univ.inv_eq]

end Spherical

end Building

end CFSG.Monster.B.Geometry
