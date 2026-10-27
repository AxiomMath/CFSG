module

public import CFSG.Monster.B.Geometry.Extension
public import CFSG.Monster.B.Geometry.Rigidity
public import CFSG.Monster.B.Geometry.ChamberSystem

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}

section DistMap

variable (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
include hδ hδ'

theorem mem_residue_iff_of_dist_eq {θ : C → C'} (hθ : ∀ x y, δ' (θ x) (θ y) = δ x y)
    (J : Set ι) (c y : C) : θ y ∈ residue cs δ' J (θ c) ↔ y ∈ residue cs δ J c := by
  rw [mem_residue_iff_mem_parabolic hδ', mem_residue_iff_mem_parabolic hδ, hθ]

theorem mem_foundation_iff_of_dist_eq {θ : C → C'} (hθ : ∀ x y, δ' (θ x) (θ y) = δ x y)
    (k : ℕ) (c y : C) : θ y ∈ foundation cs δ' k (θ c) ↔ y ∈ foundation cs δ k c := by
  simp only [mem_foundation_iff, mem_residue_iff_of_dist_eq hδ hδ' hθ]

theorem mapsTo_foundation_union {θ : C → C'} (hθ : ∀ x y, δ' (θ x) (θ y) = δ x y) (k : ℕ)
    (c d : C) :
    Set.MapsTo θ (foundation cs δ k c ∪ {d}) (foundation cs δ' k (θ c) ∪ {θ d}) := by
  rintro y (hy | hy)
  · exact Or.inl ((mem_foundation_iff_of_dist_eq hδ hδ' hθ k c y).mpr hy)
  · rw [Set.mem_singleton_iff.mp hy]
    exact Or.inr rfl

theorem surjOn_foundation_union {θ : C → C'} (hθ : ∀ x y, δ' (θ x) (θ y) = δ x y)
    (hs : Function.Surjective θ) (k : ℕ) (c d : C) :
    Set.SurjOn θ (foundation cs δ k c ∪ {d}) (foundation cs δ' k (θ c) ∪ {θ d}) := by
  rintro z (hz | hz)
  · obtain ⟨y, rfl⟩ := hs z
    exact ⟨y, Or.inl ((mem_foundation_iff_of_dist_eq hδ hδ' hθ k c y).mp hz), rfl⟩
  · exact ⟨d, Or.inr rfl, (Set.mem_singleton_iff.mp hz).symm⟩

end DistMap

theorem IsTypeIso.dist_eq_univ (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {ψ : C → C'}
    (hψ : IsTypeIso cs δ δ' Set.univ Set.univ ψ) (x y : C) : δ' (ψ x) (ψ y) = δ x y := by
  have h : residue cs δ Set.univ x = Set.univ := residue_univ hδ x
  refine IsTypeIso.dist_eq hδ hδ' (J := Set.univ) (a := x) (X' := Set.univ) ?_
    (self_mem_residue _ x) (by rw [h]; trivial)
  rw [h]
  exact hψ

theorem IsTypeIso.comp {C'' : Type*} {δ'' : C'' → C'' → W} {ψ : C → C'} {χ : C' → C''}
    (hψ : IsTypeIso cs δ δ' Set.univ Set.univ ψ) (hχ : IsTypeIso cs δ' δ'' Set.univ Set.univ χ) :
    IsTypeIso cs δ δ'' Set.univ Set.univ (χ ∘ ψ) :=
  ⟨hχ.1.comp hψ.1, fun x _ y _ i => (hχ.2 _ trivial _ trivial i).trans (hψ.2 x trivial y trivial i)⟩

theorem isTypeIso_of_mem_typeAut {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) :
    IsTypeIso cs δ δ Set.univ Set.univ g :=
  ⟨Set.bijOn_univ.mpr g.bijective, fun x _ y _ i => hg x y i⟩

theorem length_dist_le_succ (hδ : IsWeylDistanceBuilding cs δ) {x x' : C} {i : ι}
    (h : δ x x' = cs.simple i) (y : C) : cs.length (δ x y) ≤ cs.length (δ x' y) + 1 := by
  have hk' := hδ.symm_of_eq_simple h
  have hinv : ∀ u v, cs.length (δ u v) = cs.length (δ v u) := fun u v => by
    rw [dist_inv hδ u v, cs.length_inv]
  rcases (hδ.mul_simple y x' x i hk').1 with h' | h'
  · rw [hinv, h', ← hinv]
    omega
  · rw [hinv, h']
    have := cs.length_mul_le (δ y x') (cs.simple i)
    rw [cs.length_simple, hinv y x'] at this
    exact this

theorem ext_of_transitive [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hrig : Rig₂ cs δ)
    (htrans : ∀ c d c₁ d₁ : C, δ c d = longest cs Set.univ → δ c₁ d₁ = longest cs Set.univ →
      ∃ g ∈ typeAut cs δ, g c = c₁ ∧ g d = d₁)
    (hreal : ∀ c d : C, δ c d = longest cs Set.univ → ∀ Ψ : C → C,
      IsWeylIsometry δ δ (foundation cs δ 2 c ∪ {d}) (foundation cs δ 2 c ∪ {d}) Ψ →
        Ψ c = c → Ψ d = d → ∃ g ∈ typeAut cs δ, Set.EqOn g Ψ (foundation cs δ 2 c ∪ {d}))
    (hδ' : IsWeylDistanceBuilding cs δ') {ψ : C → C'}
    (hψ : IsTypeIso cs δ δ' Set.univ Set.univ ψ) {c d : C} {c' d' : C'}
    (hcd : δ c d = longest cs Set.univ) (hcd' : δ' c' d' = longest cs Set.univ) {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' (foundation cs δ 2 c ∪ {d}) (foundation cs δ' 2 c' ∪ {d'}) φ)
    (hφc : φ c = c') (hφd : φ d = d') :
    ∃ F : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F ∧
      Set.EqOn F φ (foundation cs δ 2 c ∪ {d}) ∧
      ∀ F' : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F' →
        Set.EqOn F' φ (foundation cs δ 2 c ∪ {d}) → F' = F := by
  have hψd := IsTypeIso.dist_eq_univ hδ hδ' hψ
  have hψb : Function.Bijective ψ := Set.bijOn_univ.mp hψ.1
  let e : C ≃ C' := Equiv.ofBijective ψ hψb
  have he : ∀ x, e x = ψ x := fun _ => rfl
  have hχd : ∀ x y : C', δ (e.symm x) (e.symm y) = δ' x y := by
    intro x y
    rw [← hψd, ← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hopp : δ (e.symm c') (e.symm d') = longest cs Set.univ := by rw [hχd, hcd']
  obtain ⟨h, hh, hhc, hhd⟩ := htrans _ _ c d hopp hcd
  have hhd' := dist_typeAut hδ hh
  set Ψ : C → C := fun y => h (e.symm (φ y)) with hΨ
  have hΨd : ∀ y ∈ foundation cs δ 2 c ∪ {d}, ∀ z ∈ foundation cs δ 2 c ∪ {d},
      δ (Ψ y) (Ψ z) = δ y z := fun y hy z hz => by
    simp only [hΨ, hhd', hχd]
    exact hφ.2 y hy z hz
  have hΨc : Ψ c = c := by simp [hΨ, hφc, hhc]
  have hΨdd : Ψ d = d := by simp [hΨ, hφd, hhd]
  have hmaps1 := mapsTo_foundation_union hδ' hδ (θ := e.symm) hχd 2 c' d'
  have hmaps2 := mapsTo_foundation_union hδ hδ (θ := h) hhd' 2 (e.symm c') (e.symm d')
  have hsurj1 := surjOn_foundation_union hδ' hδ (θ := e.symm) hχd e.symm.surjective 2 c' d'
  have hsurj2 := surjOn_foundation_union hδ hδ (θ := h) hhd' h.surjective 2 (e.symm c')
    (e.symm d')
  rw [hhc, hhd] at hmaps2 hsurj2
  have hΨiso : IsWeylIsometry δ δ (foundation cs δ 2 c ∪ {d}) (foundation cs δ 2 c ∪ {d}) Ψ := by
    refine isWeylIsometry_of hδ hδ ?_ ?_ hΨd
    · exact hmaps2.comp (hmaps1.comp hφ.1.mapsTo)
    · exact hsurj2.comp (hsurj1.comp hφ.1.surjOn)
  obtain ⟨g, hg, hgΨ⟩ := hreal c d hcd Ψ hΨiso hΨc hΨdd
  refine ⟨fun y => ψ (h⁻¹ (g y)), ?_, ?_, ?_⟩
  · have h1 : IsTypeIso cs δ δ Set.univ Set.univ (fun y => h⁻¹ (g y)) :=
      IsTypeIso.comp (isTypeIso_of_mem_typeAut hg) (isTypeIso_of_mem_typeAut (inv_mem hh))
    exact IsTypeIso.comp h1 hψ
  · intro y hy
    simp only
    rw [hgΨ hy, hΨ]
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply, ← he, Equiv.apply_symm_apply]
  · intro F' hF' hF'φ
    have hF : IsTypeIso cs δ δ' Set.univ Set.univ (fun y => ψ (h⁻¹ (g y))) :=
      IsTypeIso.comp (IsTypeIso.comp (isTypeIso_of_mem_typeAut hg)
        (isTypeIso_of_mem_typeAut (inv_mem hh))) hψ
    have hagree : ∀ y ∈ foundation cs δ 2 c ∪ {d}, F' y = ψ (h⁻¹ (g y)) := by
      intro y hy
      rw [hF'φ hy, hgΨ hy, hΨ]
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply, ← he, Equiv.apply_symm_apply]
    refine (spherical_building_panel_opposite_rigidity hδ hrig hcd).2 F' _ hF' hF
      (hagree d (Or.inr rfl)) fun i y hy => hagree y (Or.inl ?_)
    exact residue_subset_foundation (J := {i}) (by simp) c hy

variable {F : Type*}

variable (cs δ) in
@[expose] def IsChamberModel (X : ChamberSystem ι F) (f : C → F) : Prop :=
  Function.Bijective f ∧ ∀ x y i, (δ x y = cs.simple i ↔ x ≠ y ∧ X.adj i (f x) (f y))

namespace IsChamberModel

variable {X : ChamberSystem ι F} {f : C → F} (hf : IsChamberModel cs δ X f)
include hf

@[expose] noncomputable def equiv : C ≃ F := Equiv.ofBijective f hf.1

theorem equiv_apply (x : C) : hf.equiv x = f x := rfl

@[expose] noncomputable def perm (G : Equiv.Perm F) : Equiv.Perm C :=
  (hf.equiv.trans G).trans hf.equiv.symm

theorem apply_perm (G : Equiv.Perm F) (x : C) : f (hf.perm G x) = G (f x) := by
  change hf.equiv (hf.equiv.symm (G (hf.equiv x))) = G (f x)
  rw [Equiv.apply_symm_apply]
  rfl

theorem perm_mem_typeAut {G : Equiv.Perm F} (hG : G ∈ X.typeAut) : hf.perm G ∈ typeAut cs δ := by
  intro x y i
  rw [hf.2, hf.2, hf.apply_perm, hf.apply_perm, (hf.perm G).injective.ne_iff, hG i]

theorem isTypeIso {f' : C' → F} (hf' : IsChamberModel cs δ' X f') :
    IsTypeIso cs δ δ' Set.univ Set.univ (fun x => hf'.equiv.symm (f x)) := by
  refine ⟨Set.bijOn_univ.mpr ((hf'.equiv.symm.bijective).comp hf.1), fun x _ y _ i => ?_⟩
  rw [hf'.2, hf.2]
  have h1 : ∀ z : C, f' (hf'.equiv.symm (f z)) = f z := fun z => by
    rw [← hf'.equiv_apply, Equiv.apply_symm_apply]
  rw [h1, h1, hf'.equiv.symm.injective.ne_iff, hf.1.1.ne_iff]

theorem length_le (hδ : IsWeylDistanceBuilding cs δ) {x y : C} {γ : List (ι × F)}
    (hγ : X.IsGallery (f x) γ) (hend : galleryEnd (f x) γ = f y) :
    cs.length (δ x y) ≤ γ.length := by
  induction γ generalizing x with
  | nil =>
    rw [hf.1.1 hend, hδ.eq_one_self, cs.length_one]
    exact Nat.zero_le _
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨x', hx'⟩ := hf.1.2 p.2
    rw [← hx'] at h1 h2
    have h3 := ih h2 (by rw [hx']; exact hend)
    by_cases e : x = x'
    · subst e
      simp only [List.length_cons]
      omega
    · have h4 := length_dist_le_succ hδ ((hf.2 x x' p.1).mpr ⟨e, h1⟩) y
      simp only [List.length_cons]
      omega

theorem mem_residue_iff {J : Set ι} {x y : C} :
    y ∈ residue cs δ J x ↔ f y ∈ X.residue J (f x) := by
  constructor
  · intro h
    induction h with
    | refl => exact X.self_mem_residue J (f x)
    | tail _ hbc ih =>
      obtain ⟨i, hi, hδi⟩ := hbc
      have hadj := ((hf.2 _ _ i).mp hδi).2
      exact ChamberSystem.mem_residue_trans ih (ChamberSystem.residue_mono
        (Set.singleton_subset_iff.mpr hi) _ (ChamberSystem.mem_residue_singleton.mpr hadj))
  · rintro ⟨γ, hγ, hJ, hend⟩
    induction γ generalizing x with
    | nil =>
      rw [hf.1.1 hend]
      exact self_mem_residue J y
    | cons p γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      obtain ⟨x', hx'⟩ := hf.1.2 p.2
      rw [← hx'] at h1 h2
      have h3 := ih h2 (fun i hi => hJ i (by simp [hi])) (by rw [hx']; exact hend)
      by_cases e : x = x'
      · rwa [e]
      · have hδi := (hf.2 x x' p.1).mpr ⟨e, h1⟩
        exact mem_residue_trans (Relation.ReflTransGen.single ⟨p.1, hJ p.1 (by simp), hδi⟩) h3

end IsChamberModel

end CFSG.Monster.B.Geometry
