module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

structure GenFixedRootDatum (τ : Tag) (p₀ : ℕ) [Fact p₀.Prime] (k : Type)
    [Field k] [CharP k p₀] [IsAlgClosed k] (M : Type) [CommGroup M] where
  simplyLaced : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8
  e : ℕ
  one_le_e : 1 ≤ e
  χ : Multiplicative (Fin τ.rank → ℤ) →* M
  θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)
  isometry : ∀ x y, rform (θ x) (θ y) = rform x y
  bijOn_kernelRoots : Set.BijOn θ (toReal '' kernelRoots χ) (toReal '' kernelRoots χ)
  bijOn_simpleRoots :
    Set.BijOn θ (toReal '' unionSimpleRoots χ Set.univ) (toReal '' unionSimpleRoots χ Set.univ)
  orbit_orthogonal : ∀ α ∈ kernelRoots χ, ∀ β ∈ thetaOrbit θ α, ∀ γ ∈ thetaOrbit θ α, β ≠ γ →
    iform β γ = 0
  orbit_reflection : ∀ α ∈ kernelRoots χ,
    ∃ w ∈ Subgroup.closure ((fun β => setReflection (thetaOrbit θ β)) ''
      unionSimpleRoots χ Set.univ),
      ∃ β ∈ unionSimpleRoots χ Set.univ, (fun γ => w • γ) '' thetaOrbit θ α = thetaOrbit θ β
  F : MulAut (adjointGroup τ k)
  map_torusGroup : ((torusGroup τ k).subgroupOf (adjointGroup τ k)).map F.toMonoidHom =
    (torusGroup τ k).subgroupOf (adjointGroup τ k)
  map_rootSubgroup : ∀ α ∈ kernelRoots χ, ∀ α' : Fin τ.rank → ℤ, θ (toReal α) = toReal α' →
    ((rootSubgroup τ k α).subgroupOf (adjointGroup τ k)).map F.toMonoidHom =
      (rootSubgroup τ k α').subgroupOf (adjointGroup τ k)
  map_rootSL2 : ∀ β ∈ unionSimpleRoots χ Set.univ, ∀ β' : Fin τ.rank → ℤ,
    θ (toReal β) = toReal β' → ∀ (A : SL2 k) (x : adjointGroup τ k),
      (x : ModGL τ k) = rootSL2 τ k β A →
        (F x : ModGL τ k) =
          rootSL2 τ k β' (Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ e) A)
  J : Set (KernelComponent χ)
  isThetaOrbit : ∃ i₀ : KernelComponent χ, J = {i | ∃ m : ℕ, ∃ α ∈ componentRoots χ i₀,
    ∃ β ∈ componentRoots χ i, (θ ^ m) (toReal α) = toReal β}

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

@[expose] def q : ℕ :=
  p₀ ^ D.e

@[expose] def roots : Set (Fin τ.rank → ℤ) :=
  unionRoots D.χ D.J

@[expose] def posRootsJ : Set (Fin τ.rank → ℤ) :=
  posRoots D.roots

@[expose] def simpleRootsJ : Set (Fin τ.rank → ℤ) :=
  unionSimpleRoots D.χ Set.univ ∩ D.roots

@[expose] def rootSpanJ : Subgroup (ModGL τ k) :=
  unionRootSpan k D.χ D.J

@[expose] def torusJ : Subgroup (ModGL τ k) :=
  unionTorus k D.χ D.J

@[expose] def unipotentJ : Subgroup (ModGL τ k) :=
  unionUnipotent k D.χ D.J

@[expose] def fixedGroup : Subgroup (adjointGroup τ k) :=
  D.rootSpanJ.subgroupOf (adjointGroup τ k) ⊓ D.F.toMonoidHom.eqLocus (MonoidHom.id _)

@[expose] def fixedUnipotent : Subgroup (adjointGroup τ k) :=
  D.unipotentJ.subgroupOf (adjointGroup τ k) ⊓ D.F.toMonoidHom.eqLocus (MonoidHom.id _)

@[expose] def orbits : Set (Set (Fin τ.rank → ℤ)) :=
  {O | ∃ β ∈ D.simpleRootsJ, O = thetaOrbit D.θ β}

@[expose] def orbitRoot (O : Set (Fin τ.rank → ℤ)) : Fin τ.rank → ℤ :=
  lexLeast O

@[expose] def orbitCard (O : Set (Fin τ.rank → ℤ)) : ℕ :=
  O.ncard

@[expose] def orbitField (O : Set (Fin τ.rank → ℤ)) : Subfield k :=
  frobeniusFixedField k p₀ (D.e * orbitCard O)

@[expose] def orbitMap (O : Set (Fin τ.rank → ℤ)) (A : SL2 (D.orbitField O)) : ModGL τ k :=
  ((List.range (orbitCard O)).map fun j => rootSL2 τ k (thetaPowVec D.θ j (orbitRoot O))
    (Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * j))
      (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A))).prod

@[expose] def orbitX (O : Set (Fin τ.rank → ℤ)) (c : D.orbitField O) : ModGL τ k :=
  D.orbitMap O (uSL c)

@[expose] def orbitY (O : Set (Fin τ.rank → ℤ)) (c : D.orbitField O) : ModGL τ k :=
  D.orbitMap O (vSL c)

@[expose] def orbitH (O : Set (Fin τ.rank → ℤ)) (t : (D.orbitField O)ˣ) : ModGL τ k :=
  D.orbitMap O (HSL t)

@[expose] def orbitN (O : Set (Fin τ.rank → ℤ)) : ModGL τ k :=
  D.orbitMap O WSL

@[expose] def orbitGroup : Subgroup (ModGL τ k) :=
  Subgroup.closure {g | ∃ O ∈ D.orbits, ∃ c : D.orbitField O, g = D.orbitX O c ∨ g = D.orbitY O c}

@[expose] def orbitTorus : Subgroup (ModGL τ k) :=
  D.orbitGroup ⊓ torusGroup τ k

@[expose] def orbitBorel : Subgroup (ModGL τ k) :=
  D.orbitGroup ⊓ borelGroup τ k

theorem finite_kernelRoots : (kernelRoots D.χ).Finite :=
  (root_character_kernel_orthogonal_central_product τ k D.χ).1

theorem finite_kernelComponent : Finite (KernelComponent D.χ) :=
  (root_character_kernel_orthogonal_central_product τ k D.χ).2.1

theorem theta_injective : Function.Injective D.θ := by
  intro x y h
  by_contra hne
  have hpos := rform_self_pos (τ := τ) (sub_ne_zero.2 hne)
  have e := D.isometry (x - y) (x - y)
  rw [map_sub, h, sub_self] at e
  have h0 : rform (τ := τ) 0 0 = 0 := by simp [rform]
  rw [h0] at e
  linarith

theorem mk_eq_of_theta {a b : kernelRoots D.χ} (hab : (⟦a⟧ : KernelComponent D.χ) = ⟦b⟧)
    {a' b' : kernelRoots D.χ} (ha : D.θ (toReal a) = toReal a')
    (hb : D.θ (toReal b) = toReal b') : (⟦a'⟧ : KernelComponent D.χ) = ⟦b'⟧ := by
  have h : Relation.EqvGen (fun α β : kernelRoots D.χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) a b :=
    Quotient.exact hab
  clear hab
  induction h generalizing a' b' with
  | rel x y hxy =>
    apply mk_eq_of_iform_ne_zero
    rw [dotProduct_mulVec_eq_iform] at hxy
    have e := D.isometry (toReal x) (toReal y)
    rw [ha, hb, rform_toReal, rform_toReal] at e
    have e' : iform (a' : Fin τ.rank → ℤ) b' = iform (x : Fin τ.rank → ℤ) y := by
      exact_mod_cast e
    rw [e']
    exact hxy
  | refl x =>
    have : a' = b' := Subtype.ext (toReal_injective (ha.symm.trans hb))
    rw [this]
  | symm x y _ ih => exact (ih hb ha).symm
  | trans x y z _ _ ih₁ ih₂ =>
    obtain ⟨y', hy', e⟩ := D.bijOn_kernelRoots.mapsTo ⟨_, y.2, rfl⟩
    exact (ih₁ (b' := ⟨y', hy'⟩) ha e.symm).trans (ih₂ e.symm hb)

theorem J_nonempty : D.J.Nonempty := by
  obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
  obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep i₀
  refine ⟨⟦⟨α, hα⟩⟧, ?_⟩
  rw [hJ]
  exact ⟨0, α, ⟨hα, rfl⟩, α, ⟨hα, rfl⟩, by simp⟩

theorem mapsTo_roots : Set.MapsTo D.θ (toReal '' D.roots) (toReal '' D.roots) := by
  obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
  rintro _ ⟨α, ⟨hα, hαJ⟩, rfl⟩
  obtain ⟨α', hα', e⟩ := D.bijOn_kernelRoots.mapsTo ⟨α, hα, rfl⟩
  refine ⟨α', ⟨hα', ?_⟩, e⟩
  change (⟦⟨α, hα⟩⟧ : KernelComponent D.χ) ∈ D.J at hαJ
  rw [hJ] at hαJ ⊢
  obtain ⟨m, α₀, hα₀, β, ⟨hβ, hβc⟩, hm⟩ := hαJ
  obtain ⟨β', hβ', e'⟩ := D.bijOn_kernelRoots.mapsTo ⟨β, hβ, rfl⟩
  refine ⟨m + 1, α₀, hα₀, β', ⟨hβ', D.mk_eq_of_theta hβc e'.symm e.symm⟩, ?_⟩
  rw [pow_succ', Module.End.mul_apply, hm, e']

theorem finite_roots : D.roots.Finite :=
  D.finite_kernelRoots.subset fun _ hα => hα.1

theorem bijOn_roots : Set.BijOn D.θ (toReal '' D.roots) (toReal '' D.roots) :=
  (Set.Finite.injOn_iff_bijOn_of_mapsTo (D.finite_roots.image _) D.mapsTo_roots).1
    D.theta_injective.injOn

theorem simpleRootsJ_eq : D.simpleRootsJ = unionSimpleRoots D.χ D.J := by
  ext β
  constructor
  · rintro ⟨⟨i, -, hβi⟩, hβΨ⟩
    obtain ⟨j, hj, hβj⟩ := mem_unionRoots_iff.1 hβΨ
    rw [eq_of_mem_componentRoots (simpleRoots_subset hβi) hβj] at hβi
    exact ⟨j, hj, hβi⟩
  · rintro ⟨i, hi, hβi⟩
    exact ⟨⟨i, Set.mem_univ i, hβi⟩, componentRoots_subset_unionRoots hi (simpleRoots_subset hβi)⟩

theorem mapsTo_simpleRootsJ :
    Set.MapsTo D.θ (toReal '' D.simpleRootsJ) (toReal '' D.simpleRootsJ) := by
  rintro _ ⟨β, ⟨hβΔ, hβΨ⟩, rfl⟩
  obtain ⟨β₁, hβ₁, e₁⟩ := D.bijOn_simpleRoots.mapsTo ⟨β, hβΔ, rfl⟩
  obtain ⟨β₂, hβ₂, e₂⟩ := D.mapsTo_roots ⟨β, hβΨ, rfl⟩
  have h12 : β₁ = β₂ := toReal_injective (e₁.trans e₂.symm)
  subst h12
  exact ⟨β₁, ⟨hβ₁, hβ₂⟩, e₁⟩

theorem bijOn_simpleRootsJ :
    Set.BijOn D.θ (toReal '' D.simpleRootsJ) (toReal '' D.simpleRootsJ) :=
  (Set.Finite.injOn_iff_bijOn_of_mapsTo ((D.finite_roots.subset Set.inter_subset_right).image _)
    D.mapsTo_simpleRootsJ).1 D.theta_injective.injOn

theorem mem_posRootsJ_of_theta {α α' : Fin τ.rank → ℤ} (hα : α ∈ D.posRootsJ)
    (hα' : α' ∈ D.roots) (h : D.θ (toReal α) = toReal α') : α' ∈ D.posRootsJ :=
  mem_posRoots_of_theta (J := D.J) (by rw [← D.simpleRootsJ_eq]; exact D.mapsTo_simpleRootsJ)
    hα hα' h

theorem bijOn_posRootsJ : Set.BijOn D.θ (toReal '' D.posRootsJ) (toReal '' D.posRootsJ) := by
  have hmaps : Set.MapsTo D.θ (toReal '' D.posRootsJ) (toReal '' D.posRootsJ) := by
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨α', hα', e⟩ := D.mapsTo_roots ⟨α, hα.1, rfl⟩
    exact ⟨α', D.mem_posRootsJ_of_theta hα hα' e.symm, e⟩
  exact (Set.Finite.injOn_iff_bijOn_of_mapsTo
    ((D.finite_roots.subset fun _ hα => hα.1).image _) hmaps).1 D.theta_injective.injOn

theorem map_rootSpan_subgroupOf {S : Set (Fin τ.rank → ℤ)} (hS : S ⊆ kernelRoots D.χ)
    (hθS : Set.BijOn D.θ (toReal '' S) (toReal '' S)) :
    ((rootSpan τ k S).subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom =
      (rootSpan τ k S).subgroupOf (adjointGroup τ k) := by
  have hF : ∀ α ∈ S, ∀ α' : Fin τ.rank → ℤ, D.θ (toReal α) = toReal α' →
      ∀ x : adjointGroup τ k, (x : ModGL τ k) ∈ rootSubgroup τ k α →
        (D.F x : ModGL τ k) ∈ rootSubgroup τ k α' := by
    intro α hα α' h x hx
    have h1 : D.F x ∈ ((rootSubgroup τ k α).subgroupOf (adjointGroup τ k)).map
        D.F.toMonoidHom := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    rw [D.map_rootSubgroup α (hS hα) α' h] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hF' : ∀ α ∈ S, ∀ α' : Fin τ.rank → ℤ, D.θ (toReal α) = toReal α' →
      ∀ x : adjointGroup τ k, (x : ModGL τ k) ∈ rootSubgroup τ k α' →
        (D.F.symm x : ModGL τ k) ∈ rootSubgroup τ k α := by
    intro α hα α' h x hx
    have h1 : x ∈ ((rootSubgroup τ k α).subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom := by
      rw [D.map_rootSubgroup α (hS hα) α' h]
      exact Subgroup.mem_subgroupOf.2 hx
    obtain ⟨y, hy, rfl⟩ := h1
    simpa using Subgroup.mem_subgroupOf.1 hy
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_subgroupOf.2 (coe_mulAut_mem_rootSpan D.F (fun α hα y hy => ?_)
      (Subgroup.mem_subgroupOf.1 hx))
    obtain ⟨α', hα', e⟩ := hθS.mapsTo ⟨α, hα, rfl⟩
    exact (le_iSup₂_of_le α' hα' le_rfl : rootSubgroup τ k α' ≤ rootSpan τ k S)
      (hF α hα α' e.symm y hy)
  · intro y hy
    refine ⟨D.F.symm y, Subgroup.mem_subgroupOf.2 (coe_mulAut_mem_rootSpan D.F.symm
      (fun α' hα' z hz => ?_) (Subgroup.mem_subgroupOf.1 hy)), by simp⟩
    obtain ⟨_, ⟨α, hα, rfl⟩, e⟩ := hθS.surjOn ⟨α', hα', rfl⟩
    exact (le_iSup₂_of_le α hα le_rfl : rootSubgroup τ k α ≤ rootSpan τ k S)
      (hF' α hα α' e z hz)

theorem map_rootSpanJ :
    (D.rootSpanJ.subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom =
      D.rootSpanJ.subgroupOf (adjointGroup τ k) :=
  D.map_rootSpan_subgroupOf (fun _ hα => hα.1) D.bijOn_roots

theorem map_unipotentJ :
    (D.unipotentJ.subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom =
      D.unipotentJ.subgroupOf (adjointGroup τ k) :=
  D.map_rootSpan_subgroupOf (fun _ hα => hα.1.1) D.bijOn_posRootsJ

theorem map_torusJ :
    (D.torusJ.subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom =
      D.torusJ.subgroupOf (adjointGroup τ k) := by
  have hS := D.map_rootSpanJ
  have hH := D.map_torusGroup
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.1 hx
    have h1 : D.F x ∈ (D.rootSpanJ.subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom :=
      ⟨x, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 hx').1, rfl⟩
    have h2 : D.F x ∈ ((torusGroup τ k).subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom :=
      ⟨x, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 hx').2, rfl⟩
    rw [hS] at h1
    rw [hH] at h2
    exact Subgroup.mem_subgroupOf.2
      (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 h1, Subgroup.mem_subgroupOf.1 h2⟩)
  · intro hy
    have hy' := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)
    have h1 : y ∈ (D.rootSpanJ.subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom := by
      rw [hS]
      exact Subgroup.mem_subgroupOf.2 hy'.1
    have h2 : y ∈ ((torusGroup τ k).subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom := by
      rw [hH]
      exact Subgroup.mem_subgroupOf.2 hy'.2
    obtain ⟨x, hx, rfl⟩ := h1
    obtain ⟨x', hx', hxx'⟩ := h2
    have hx'x : x' = x := D.F.injective hxx'
    subst hx'x
    exact ⟨x', Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
      ⟨Subgroup.mem_subgroupOf.1 hx, Subgroup.mem_subgroupOf.1 hx'⟩), rfl⟩

theorem pow_apply_mem_kernelRoots {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ) (m : ℕ) :
    (D.θ ^ m) (toReal α) ∈ toReal '' kernelRoots D.χ := by
  induction m with
  | zero => exact ⟨α, hα, by simp⟩
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact D.bijOn_kernelRoots.mapsTo ih

theorem thetaOrbit_subset_kernelRoots {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ) :
    thetaOrbit D.θ α ⊆ kernelRoots D.χ := by
  rintro γ ⟨m, hm⟩
  obtain ⟨γ', hγ', e⟩ := D.pow_apply_mem_kernelRoots hα m
  rw [hm] at e
  rwa [toReal_injective e] at hγ'

theorem thetaPowVec_spec {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ) (j : ℕ) :
    toReal (thetaPowVec D.θ j α) = (D.θ ^ j) (toReal α) ∧
      thetaPowVec D.θ j α ∈ thetaOrbit D.θ α ∧ thetaPowVec D.θ j α ∈ kernelRoots D.χ := by
  obtain ⟨γ, hγ, e⟩ := D.pow_apply_mem_kernelRoots hα j
  rw [thetaPowVec_eq e]
  exact ⟨e, ⟨j, e.symm⟩, hγ⟩

theorem finite_thetaOrbit {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ) :
    (thetaOrbit D.θ α).Finite :=
  D.finite_kernelRoots.subset (D.thetaOrbit_subset_kernelRoots hα)

theorem pairwise_commute_thetaOrbit {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ) :
    (thetaOrbit D.θ α).Pairwise fun β γ => Commute (rootReflection β) (rootReflection γ) :=
  fun β hβ γ hγ hne => commute_rootReflection_of_iform_eq_zero
    (D.thetaOrbit_subset_kernelRoots hα hβ).1 (D.thetaOrbit_subset_kernelRoots hα hγ).1
    (D.orbit_orthogonal α hα β hβ γ hγ hne)

theorem setReflection_thetaOrbit_eq_list_prod {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ)
    {l : List (Fin τ.rank → ℤ)} (hl : l.Nodup) (hlO : ∀ β, β ∈ l ↔ β ∈ thetaOrbit D.θ α) :
    setReflection (thetaOrbit D.θ α) = (l.map rootReflection).prod :=
  setReflection_eq_list_prod (D.finite_thetaOrbit hα) (D.pairwise_commute_thetaOrbit hα) hl hlO

theorem mem_kernelRoots_of_mem_simpleRootsJ {β : Fin τ.rank → ℤ} (hβ : β ∈ D.simpleRootsJ) :
    β ∈ kernelRoots D.χ :=
  hβ.2.1

theorem orbitRoot_mem {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) : orbitRoot O ∈ O := by
  obtain ⟨β, hβ, rfl⟩ := hO
  exact lexLeast_mem (D.finite_thetaOrbit (D.mem_kernelRoots_of_mem_simpleRootsJ hβ))
    ⟨β, self_mem_thetaOrbit _ _⟩

theorem orbitCard_pos {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) : 0 < orbitCard O := by
  obtain ⟨β, hβ, rfl⟩ := hO
  exact (Set.ncard_pos (D.finite_thetaOrbit (D.mem_kernelRoots_of_mem_simpleRootsJ hβ))).2
    ⟨β, self_mem_thetaOrbit _ _⟩

theorem mem_orbitField {O : Set (Fin τ.rank → ℤ)} {c : k} :
    c ∈ D.orbitField O ↔ c ^ D.q ^ orbitCard O = c := by
  rw [orbitField, mem_frobeniusFixedField, q, pow_mul]

theorem card_orbitField {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Nat.card (D.orbitField O) = D.q ^ orbitCard O := by
  rw [orbitField, card_frobeniusFixedField (Nat.mul_pos D.one_le_e (D.orbitCard_pos hO)), q,
    pow_mul]

end GenFixedRootDatum

end CFSG.RankThree.Lattice
