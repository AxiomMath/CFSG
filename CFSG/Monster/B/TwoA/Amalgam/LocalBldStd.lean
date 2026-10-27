module

public import CFSG.Monster.B.E6.StdF4UnitModel
public import CFSG.Monster.B.Geometry.ResidueTransfer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
  CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.Geometry

section Model

variable {ι : Type*} {M M' : CoxeterMatrix ι} {W W' : Type*} [Group W] [Group W']
  {cs : CoxeterSystem M W} {cs' : CoxeterSystem M' W'} {C F : Type*} {δ : C → C → W}
  {δ' : C → C → W'} {L : Set ι} {x₀ : C} {Y : ChamberSystem ι F}
  {f : residue cs δ L x₀ → F} (hf : IsChamberModel cs (E6.StdF4.resDist cs δ L x₀) Y f)

@[expose] def modelChamber (a : F) : C := (hf.equiv.symm a : C)

theorem bijOn_modelChamber (hres : residue cs' δ' L x₀ = residue cs δ L x₀) :
    Set.BijOn (modelChamber hf) Set.univ (residue cs' δ' L x₀) := by
  rw [hres]
  refine ⟨fun a _ => (hf.equiv.symm a).2, fun a _ b _ h => hf.equiv.symm.injective
    (Subtype.ext h), fun y hy => ⟨hf.equiv ⟨y, hy⟩, Set.mem_univ _, ?_⟩⟩
  simp [modelChamber]

theorem modelChamber_adj_iff (hδ' : IsWeylDistanceBuilding cs' δ')
    (hsimple : ∀ x y j, δ' x y = cs'.simple j ↔ δ x y = cs.simple j) (a b : F) (j : ι) :
    Y.adj j a b ↔ δ' (modelChamber hf a) (modelChamber hf b) = 1 ∨
      δ' (modelChamber hf a) (modelChamber hf b) = cs'.simple j := by
  have h1 : modelChamber hf a = modelChamber hf b ↔ a = b :=
    ⟨fun h => hf.equiv.symm.injective (Subtype.ext h), fun h => h ▸ rfl⟩
  have h2 := hf.2 (hf.equiv.symm a) (hf.equiv.symm b) j
  rw [← hf.equiv_apply, ← hf.equiv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  rw [hδ'.eq_one_iff, h1, hsimple]
  change Y.adj j a b ↔ a = b ∨ E6.StdF4.resDist cs δ L x₀ _ _ = cs.simple j
  rw [h2, (hf.equiv.symm.injective.ne_iff)]
  constructor
  · intro h
    by_cases e : a = b
    · exact Or.inl e
    · exact Or.inr ⟨e, h⟩
  · rintro (rfl | ⟨-, h⟩)
    · exact Y.adj_refl j a
    · exact h

variable (hδ' : IsWeylDistanceBuilding cs' δ') (hres : residue cs' δ' L x₀ = residue cs δ L x₀)
  (hsimple : ∀ x y j, δ' x y = cs'.simple j ↔ δ x y = cs.simple j)
include hf hδ' hres

theorem isBuildingOn_modelChamber :
    IsBuildingOn cs' (fun a b => δ' (modelChamber hf a) (modelChamber hf b)) L Set.univ :=
  isBuildingOn_residue_comap hδ' L x₀ (bijOn_modelChamber hf hres)

include hsimple

theorem image_panel_modelChamber (a : F) {j : ι} (hj : j ∈ L) :
    modelChamber hf '' {b | Y.adj j a b} = panel cs' δ' j (modelChamber hf a) := by
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Set.mem_ofPred_eq, modelChamber_adj_iff hf hδ' hsimple a b j] at hb
    exact (mem_panel_iff hδ').mpr hb
  · intro hy
    have hR : y ∈ residue cs' δ' L x₀ := by
      have ha := (bijOn_modelChamber hf hres).mapsTo (Set.mem_univ a)
      rw [← residue_eq_of_mem hδ' ha]
      exact residue_mono (Set.singleton_subset_iff.mpr hj) _ hy
    obtain ⟨b, -, rfl⟩ := (bijOn_modelChamber hf hres).surjOn hR
    refine ⟨b, ?_, rfl⟩
    rw [Set.mem_ofPred_eq, modelChamber_adj_iff hf hδ' hsimple a b j]
    exact (mem_panel_iff hδ').mp hy

theorem encard_panel_modelChamber (a : F) {j : ι} (hj : j ∈ L) :
    {b | Y.adj j a b}.encard = (panel cs' δ' j (modelChamber hf a)).encard := by
  rw [← image_panel_modelChamber hf hδ' hres hsimple a hj,
    ((bijOn_modelChamber hf hres).injOn.mono (Set.subset_univ _)).encard_image]

theorem exists_gallery_of_isChamberModel (a b : F) :
    ∃ γ : List (ι × F), Y.IsGallery a γ ∧ (∀ j ∈ galleryType γ, j ∈ L) ∧ galleryEnd a γ = b := by
  obtain ⟨γ, hγ, hJ, hend, -⟩ := (isBuildingOn_modelChamber hf hδ' hres).exists_gallery Y
    (fun a _ b _ j _ h => (modelChamber_adj_iff hf hδ' hsimple a b j).mpr (Or.inr h))
    (Set.mem_univ a) (Set.mem_univ b)
  exact ⟨γ, hγ, hJ, hend⟩

end Model

theorem firstJ_eq : firstJ = {j : Fin 4 | j ≠ 0} := by
  ext j
  fin_cases j <;> simp [firstJ]

theorem fourthJ_eq : FourthResidue.fourthJ = {j : Fin 4 | j ≠ 3} := by
  ext j
  fin_cases j <;> simp [FourthResidue.fourthJ]

theorem isBuildingOn_of_eq_types {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W]
    {cs : CoxeterSystem M W} {C : Type*} {δ : C → C → W} {J J' : Set ι} {R : Set C}
    (h : IsBuildingOn cs δ J R) (e : J = J') : IsBuildingOn cs δ J' R :=
  e ▸ h

abbrev unitChamber :
    PFlag UData → stdChamber := modelChamber E6.StdF4.isChamberModel_modelU

@[expose] def unitDist
    (a b : PFlag UData) : relWeylTwist TwistTag.E6 :=
  stdDistance (unitChamber a) (unitChamber b)

theorem isBuildingOn_unitDist :
    IsBuildingOn nativeCoxeterSystem unitDist {j | j ≠ 0} Set.univ :=
  isBuildingOn_of_eq_types (isBuildingOn_modelChamber E6.StdF4.isChamberModel_modelU
    isWeylDistanceBuilding_stdDistance rfl) firstJ_eq

theorem unitDist_adj_iff
    (a b : PFlag UData) (j : Fin 4) :
    (polarChamber UData (3 : Fin 4) 2 1).adj j a b ↔
      unitDist a b = 1 ∨ unitDist a b = nativeCoxeterSystem.simple j :=
  modelChamber_adj_iff E6.StdF4.isChamberModel_modelU isWeylDistanceBuilding_stdDistance
    (fun _ _ _ => Iff.rfl) a b j

theorem encard_unit_panel
    (a : PFlag UData) {j : Fin 4} (hj : j ≠ 0) :
    {b | (polarChamber UData (3 : Fin 4) 2 1).adj j a b}.encard =
      if (j : ℕ) < 2 then 3 else 5 := by
  rw [encard_panel_modelChamber E6.StdF4.isChamberModel_modelU
    isWeylDistanceBuilding_stdDistance rfl (fun _ _ _ => Iff.rfl) a
    (by rw [firstJ_eq]; exact hj)]
  exact encard_panel_stdDistance j _

theorem exists_unit_gallery
    (a b : PFlag UData) :
    ∃ γ : List (Fin 4 × PFlag UData), (polarChamber UData (3 : Fin 4) 2 1).IsGallery a γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ 0}) ∧ galleryEnd a γ = b := by
  obtain ⟨γ, h1, h2, h3⟩ := exists_gallery_of_isChamberModel E6.StdF4.isChamberModel_modelU
    isWeylDistanceBuilding_stdDistance rfl (fun _ _ _ => Iff.rfl) a b
  exact ⟨γ, h1, fun j hj => by simpa [firstJ_eq] using h2 j hj, h3⟩

abbrev orthChamber :
    PFlag OData → stdChamber := modelChamber E6.StdF4.isChamberModel_modelO

@[expose] def orthDist
    (a b : PFlag OData) : relWeylTwist TwistTag.E6 :=
  stdDistance (orthChamber a) (orthChamber b)

theorem isBuildingOn_orthDist :
    IsBuildingOn nativeCoxeterSystem orthDist {j | j ≠ 3} Set.univ :=
  isBuildingOn_of_eq_types (isBuildingOn_modelChamber E6.StdF4.isChamberModel_modelO
    isWeylDistanceBuilding_stdDistance rfl) fourthJ_eq

theorem orthDist_adj_iff
    (a b : PFlag OData) (j : Fin 4) :
    (polarChamber OData (0 : Fin 4) 1 2).adj j a b ↔
      orthDist a b = 1 ∨ orthDist a b = nativeCoxeterSystem.simple j :=
  modelChamber_adj_iff E6.StdF4.isChamberModel_modelO isWeylDistanceBuilding_stdDistance
    (fun _ _ _ => Iff.rfl) a b j

theorem encard_orth_panel
    (a : PFlag OData) {j : Fin 4} (hj : j ≠ 3) :
    {b | (polarChamber OData (0 : Fin 4) 1 2).adj j a b}.encard =
      if (j : ℕ) < 2 then 3 else 5 := by
  rw [encard_panel_modelChamber E6.StdF4.isChamberModel_modelO
    isWeylDistanceBuilding_stdDistance rfl (fun _ _ _ => Iff.rfl) a
    (by rw [fourthJ_eq]; exact hj)]
  exact encard_panel_stdDistance j _

theorem exists_orth_gallery
    (a b : PFlag OData) :
    ∃ γ : List (Fin 4 × PFlag OData), (polarChamber OData (0 : Fin 4) 1 2).IsGallery a γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ 3}) ∧ galleryEnd a γ = b := by
  obtain ⟨γ, h1, h2, h3⟩ := exists_gallery_of_isChamberModel E6.StdF4.isChamberModel_modelO
    isWeylDistanceBuilding_stdDistance rfl (fun _ _ _ => Iff.rfl) a b
  exact ⟨γ, h1, fun j hj => by simpa [fourthJ_eq] using h2 j hj, h3⟩

end CFSG.Monster.B.TwoA.Amalgam
