module

public import CFSG.Monster.B.Geometry.PlaneModel
public import CFSG.Monster.B.Geometry.QuadrangleModel

public section

namespace CFSG.Monster.B.E6.StdF4

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {F : Type*}

section Residue

variable (cs δ) in
@[expose] def resDist (L : Set ι) (x₀ : C) (a b : residue cs δ L x₀) : W := δ a b

variable {L : Set ι} {x₀ : C}

theorem image_residue_resDist {J : Set ι} (hJ : J ⊆ L) (y : residue cs δ L x₀) :
    Subtype.val '' residue cs (resDist cs δ L x₀) J y = residue cs δ J y := by
  ext z
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact Relation.ReflTransGen.lift Subtype.val (fun a b h => h) _ _ hz
  · intro hz
    have key : ∀ z', Relation.ReflTransGen (fun a b => ∃ i ∈ J, δ a b = cs.simple i) y.1 z' →
        ∃ h : z' ∈ residue cs δ L x₀, (⟨z', h⟩ : residue cs δ L x₀) ∈
          residue cs (resDist cs δ L x₀) J y := by
      intro z' hz'
      induction hz' with
      | refl => exact ⟨y.2, Relation.ReflTransGen.refl⟩
      | @tail b c _ hbc ih =>
        obtain ⟨hb, hbR⟩ := ih
        have hc : c ∈ residue cs δ L x₀ := by
          refine mem_residue_trans hb ?_
          obtain ⟨i, hi, h⟩ := hbc
          exact Relation.ReflTransGen.single ⟨i, hJ hi, h⟩
        exact ⟨hc, Relation.ReflTransGen.tail hbR hbc⟩
    obtain ⟨h, hzR⟩ := key z hz
    exact ⟨_, hzR, rfl⟩

@[expose] noncomputable def extendRes [Nonempty F] (f : residue cs δ L x₀ → F) (c : C) : F :=
  open _root_.Classical in if h : c ∈ residue cs δ L x₀ then f ⟨c, h⟩ else Classical.arbitrary F

theorem extendRes_val [Nonempty F] (f : residue cs δ L x₀ → F) (y : residue cs δ L x₀) :
    extendRes f y.1 = f y := by
  rw [extendRes, dite_eq_left y.2]

theorem IsModelResidue.ofResidue [Nonempty F] {r₁ r₂ : F → F → Prop} {i j : ι}
    (hij : ({i, j} : Set ι) ⊆ L) {y : residue cs δ L x₀} {f : residue cs δ L x₀ → F}
    (hf : IsModelResidue cs (resDist cs δ L x₀) r₁ r₂ i j y f) :
    IsModelResidue cs δ r₁ r₂ i j y.1 (extendRes f) := by
  have himg := image_residue_resDist hij y
  have hval : ∀ z ∈ residue cs δ {i, j} y.1, ∃ z' : residue cs δ L x₀,
      z' ∈ residue cs (resDist cs δ L x₀) {i, j} y ∧ z'.1 = z := fun z hz => by
    rw [← himg] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact ⟨z', hz', rfl⟩
  refine ⟨⟨fun _ _ => Set.mem_univ _, fun a ha b hb e => ?_, fun F' _ => ?_⟩, fun a ha b hb => ?_⟩
  · obtain ⟨a', ha', rfl⟩ := hval a ha
    obtain ⟨b', hb', rfl⟩ := hval b hb
    rw [extendRes_val, extendRes_val] at e
    exact congrArg Subtype.val (hf.1.injOn ha' hb' e)
  · obtain ⟨a', ha', e⟩ := hf.1.surjOn (Set.mem_univ F')
    refine ⟨a'.1, ?_, by rw [extendRes_val, e]⟩
    rw [← himg]
    exact ⟨a', ha', rfl⟩
  · obtain ⟨a', ha', rfl⟩ := hval a ha
    obtain ⟨b', hb', rfl⟩ := hval b hb
    rw [extendRes_val, extendRes_val]
    have h := hf.2 a' ha' b' hb'
    have hne : a' ≠ b' ↔ a'.1 ≠ b'.1 := not_congr Subtype.ext_iff
    rw [hne] at h
    exact h

theorem IsPlaneFlagResidue.ofResidue {k : Type*} [Field k] {i j : ι}
    (hij : ({i, j} : Set ι) ⊆ L) {y : residue cs δ L x₀}
    (h : IsPlaneFlagResidue cs (resDist cs δ L x₀) k i j y) :
    IsPlaneFlagResidue cs δ k i j y.1 := by
  have : Nonempty (PlaneFlag k) := ⟨PlaneFlag.c k⟩
  obtain ⟨f, hf | hf⟩ := h
  · exact ⟨_, Or.inl (IsModelResidue.ofResidue hij hf)⟩
  · exact ⟨_, Or.inr (IsModelResidue.ofResidue hij hf)⟩

theorem IsQuadrangleFlagResidue.ofResidue {i j : ι} (hij : ({i, j} : Set ι) ⊆ L)
    {y : residue cs δ L x₀} (h : IsQuadrangleFlagResidue cs (resDist cs δ L x₀) i j y) :
    IsQuadrangleFlagResidue cs δ i j y.1 := by
  obtain ⟨f, hf⟩ := h
  have : Nonempty QFlag := ⟨f y⟩
  exact ⟨_, IsModelResidue.ofResidue hij hf⟩

end Residue

section Isometry

variable (φ : C ≃ C) (hφ : ∀ a b, δ (φ a) (φ b) = δ a b)
include hφ

theorem image_residue_of_isometry (J : Set ι) (x : C) :
    φ '' residue cs δ J x = residue cs δ J (φ x) := by
  have hmap : ∀ (ψ : C ≃ C), (∀ a b, δ (ψ a) (ψ b) = δ a b) → ∀ a b,
      Relation.ReflTransGen (fun a b => ∃ i ∈ J, δ a b = cs.simple i) a b →
      Relation.ReflTransGen (fun a b => ∃ i ∈ J, δ a b = cs.simple i) (ψ a) (ψ b) :=
    fun ψ hψ a b h => Relation.ReflTransGen.lift ψ (fun a b ⟨i, hi, e⟩ => ⟨i, hi, by
      rw [hψ, e]⟩) a b h
  have hφs : ∀ a b, δ (φ.symm a) (φ.symm b) = δ a b := fun a b => by
    rw [← hφ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext y
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hmap φ hφ x y hy
  · intro hy
    refine ⟨φ.symm y, ?_, Equiv.apply_symm_apply φ y⟩
    have h := hmap φ.symm hφs _ _ hy
    rwa [Equiv.symm_apply_apply] at h

theorem IsModelResidue.map {r₁ r₂ : F → F → Prop} {i j : ι} {x : C} {f : C → F}
    (hf : IsModelResidue cs δ r₁ r₂ i j x f) :
    IsModelResidue cs δ r₁ r₂ i j (φ x) (f ∘ φ.symm) := by
  have himg := image_residue_of_isometry (cs := cs) φ hφ {i, j} x
  have hφs : ∀ a b, δ (φ.symm a) (φ.symm b) = δ a b := fun a b => by
    rw [← hφ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hmem : ∀ z, z ∈ residue cs δ {i, j} (φ x) ↔ φ.symm z ∈ residue cs δ {i, j} x := fun z => by
    rw [← himg]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rwa [Equiv.symm_apply_apply]
    · intro hz
      exact ⟨_, hz, Equiv.apply_symm_apply φ z⟩
  refine ⟨⟨fun _ _ => Set.mem_univ _, fun a ha b hb e => ?_, fun F' _ => ?_⟩, fun a ha b hb => ?_⟩
  · exact φ.symm.injective (hf.1.injOn ((hmem a).1 ha) ((hmem b).1 hb) e)
  · obtain ⟨a, ha, e⟩ := hf.1.surjOn (Set.mem_univ F')
    refine ⟨φ a, (hmem _).2 (by rwa [Equiv.symm_apply_apply]), ?_⟩
    simp only [Function.comp_apply, Equiv.symm_apply_apply, e]
  · have h := hf.2 _ ((hmem a).1 ha) _ ((hmem b).1 hb)
    rw [hφs, (Equiv.injective φ.symm).ne_iff] at h
    exact h

theorem IsPlaneFlagResidue.map {k : Type*} [Field k] {i j : ι} {x : C}
    (h : IsPlaneFlagResidue cs δ k i j x) : IsPlaneFlagResidue cs δ k i j (φ x) := by
  obtain ⟨f, hf | hf⟩ := h
  · exact ⟨_, Or.inl (IsModelResidue.map φ hφ hf)⟩
  · exact ⟨_, Or.inr (IsModelResidue.map φ hφ hf)⟩

theorem IsQuadrangleFlagResidue.map {i j : ι} {x : C} (h : IsQuadrangleFlagResidue cs δ i j x) :
    IsQuadrangleFlagResidue cs δ i j (φ x) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨_, IsModelResidue.map φ hφ hf⟩

end Isometry

section Weyl

variable {ι' : Type*} {M' : CoxeterMatrix ι'} {W' : Type*} [Group W'] {cs' : CoxeterSystem M' W'}
  {ψ : W ≃* W'} {e : ι ≃ ι'} (hs : ∀ i, ψ (cs.simple i) = cs'.simple (e i))
include hs

theorem residue_mapWeyl (J : Set ι) (x : C) :
    residue cs' (fun a b => ψ (δ a b)) (e '' J) x = residue cs δ J x := by
  have hrel : (fun a b => ∃ j ∈ e '' J, ψ (δ a b) = cs'.simple j) =
      fun a b => ∃ i ∈ J, δ a b = cs.simple i := by
    funext a b
    refine propext ⟨fun ⟨j, ⟨i, hi, hj⟩, h⟩ => ⟨i, hi, ψ.injective (by rw [h, ← hj, hs])⟩,
      fun ⟨i, hi, h⟩ => ⟨e i, ⟨i, hi, rfl⟩, by rw [h, hs]⟩⟩
  show {y | Relation.ReflTransGen _ x y} = {y | Relation.ReflTransGen _ x y}
  rw [hrel]

theorem IsModelResidue.mapWeyl {r₁ r₂ : F → F → Prop} {i j : ι} {x : C} {f : C → F}
    (hf : IsModelResidue cs δ r₁ r₂ i j x f) :
    IsModelResidue cs' (fun a b => ψ (δ a b)) r₁ r₂ (e i) (e j) x f := by
  have hres : residue cs' (fun a b => ψ (δ a b)) {e i, e j} x = residue cs δ {i, j} x := by
    rw [← residue_mapWeyl hs, Set.image_pair]
  have hsim : ∀ a b k, ψ (δ a b) = cs'.simple (e k) ↔ δ a b = cs.simple k := fun a b k => by
    rw [← hs]
    exact ψ.injective.eq_iff
  rw [IsModelResidue, hres]
  refine ⟨hf.1, fun a ha b hb => ?_⟩
  rw [hsim, hsim]
  exact hf.2 a ha b hb

theorem IsPlaneFlagResidue.mapWeyl {k : Type*} [Field k] {i j : ι} {x : C}
    (h : IsPlaneFlagResidue cs δ k i j x) :
    IsPlaneFlagResidue cs' (fun a b => ψ (δ a b)) k (e i) (e j) x := by
  obtain ⟨f, hf | hf⟩ := h
  · exact ⟨_, Or.inl (IsModelResidue.mapWeyl hs hf)⟩
  · exact ⟨_, Or.inr (IsModelResidue.mapWeyl hs hf)⟩

theorem IsQuadrangleFlagResidue.mapWeyl {i j : ι} {x : C}
    (h : IsQuadrangleFlagResidue cs δ i j x) :
    IsQuadrangleFlagResidue cs' (fun a b => ψ (δ a b)) (e i) (e j) x := by
  obtain ⟨f, hf⟩ := h
  exact ⟨_, IsModelResidue.mapWeyl hs hf⟩

end Weyl

end CFSG.Monster.B.E6.StdF4
