module

public import CFSG.Monster.B.Geometry.ChamberSystem
import CFSG.Monster.B.Geometry.StrictGallery
import CFSG.Monster.B.Geometry.ResidueAdj

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W)
  {C : Type*} (δ : C → C → W)

@[expose] def buildingSystem : ChamberSystem ι C where
  adj i := Relation.EqvGen fun a b => δ a b = cs.simple i
  equivalence _ := Relation.EqvGen.is_equivalence _

variable {cs δ}

private theorem p9uDMB_isGallery_of_isStrictGallery {x : C} {γ : List (ι × C)}
    (hγ : IsStrictGallery cs δ x γ) : (buildingSystem cs δ).IsGallery x γ := by
  induction γ generalizing x with
  | nil => trivial
  | cons p γ ih => exact ⟨Relation.EqvGen.rel x p.2 hγ.1, ih hγ.2⟩

private theorem p9uDMB_eqvGen_adj_iff (hB : IsWeylDistanceBuilding cs δ) {i : ι} {x y : C}
    (h : Relation.EqvGen (fun a b : C => δ a b = cs.simple i) x y) :
    δ x y = 1 ∨ δ x y = cs.simple i := by
  induction h with
  | rel a b hab => exact Or.inr hab
  | refl a => exact Or.inl (hB.eq_one_self a)
  | symm a b _ ih =>
      rcases ih with h | h
      · exact Or.inl (by rw [← (hB.eq_one_iff a b).mp h]; exact hB.eq_one_self a)
      · exact Or.inr (by rw [dist_inv hB a b, h, cs.inv_simple])
  | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with h1 | h1
      · rw [← (hB.eq_one_iff a b).mp h1] at ih2
        exact ih2
      · rcases ih2 with h2 | h2
        · exact Or.inr (by rw [← (hB.eq_one_iff b c).mp h2, h1])
        · rcases (hB.mul_simple a b c i h2).1 with h3 | h3
          · exact Or.inr (h3.trans h1)
          · exact Or.inl (h3.trans (by rw [h1, cs.simple_mul_simple_self]))

theorem buildingSystem_adj_iff (hB : IsWeylDistanceBuilding cs δ) {i : ι} {x y : C} :
    (buildingSystem cs δ).adj i x y ↔ δ x y = 1 ∨ δ x y = cs.simple i := by
  constructor
  · intro h
    exact p9uDMB_eqvGen_adj_iff hB h
  · rintro (h | h)
    · have hxy : x = y := (hB.eq_one_iff x y).mp h
      rw [hxy]
      exact Relation.EqvGen.refl y
    · exact Relation.EqvGen.rel x y h

private theorem p9uDMB_isStrictGallery_of_isOrdinary (hB : IsWeylDistanceBuilding cs δ)
    {x : C} {γ : List (ι × C)} (hγ : (buildingSystem cs δ).IsOrdinary x γ) :
    IsStrictGallery cs δ x γ := by
  induction γ generalizing x with
  | nil => trivial
  | cons p γ ih =>
    obtain ⟨h1, h2, h3⟩ := hγ
    rcases (buildingSystem_adj_iff hB).mp h1 with h | h
    · exact absurd ((hB.eq_one_iff x p.2).mp h) h2
    · exact ⟨h, ih h3⟩

theorem buildingSystem_residue (hB : IsWeylDistanceBuilding cs δ) (J : Set ι) (x : C) :
    (buildingSystem cs δ).residue J x = residue cs δ J x := by
  exact ChamberSystem.residue_eq_of_adj_iff hB (fun i x y => buildingSystem_adj_iff hB) J x

theorem buildingSystem_connected (hB : IsWeylDistanceBuilding cs δ) :
    (buildingSystem cs δ).Connected := by
  intro x y
  obtain ⟨ω, hω, hprod⟩ := cs.exists_isReduced (δ x y)
  obtain ⟨γ, hγ, -, hend⟩ := exists_strictGallery hB hω hprod.symm
  exact ⟨γ, p9uDMB_isGallery_of_isStrictGallery hγ, hend⟩

theorem buildingSystem_simplyTwoConnected (hB : IsWeylDistanceBuilding cs δ) :
    (buildingSystem cs δ).SimplyTwoConnected := by
  intro x γ hγ hclosed
  have hres : ∀ s t : ι, s ≠ t → ∀ y : C,
      (buildingSystem cs δ).IsResidueBuilding cs {s, t} y := by
    intro s t _ y
    refine ⟨δ, ?_, ?_⟩
    · rw [buildingSystem_residue hB {s, t} y]
      exact isBuildingOn_residue hB {s, t} y
    · intro a _ b _ j _
      exact buildingSystem_adj_iff hB
  obtain ⟨γ₁, h1, -, h3⟩ := ChamberSystem.exists_isOrdinary_of_isGallery hγ
  obtain ⟨γ₂, h4, h5⟩ := ChamberSystem.exists_reduction hres h1
  have hTwo : (buildingSystem cs δ).TwoHomotopic x γ γ₂ :=
    (ChamberSystem.TwoHomotopic.iff_reflTransGen.mpr
      (Relation.ReflTransGen.mono (fun _ _ h => ChamberSystem.ConstantDeletion.elemMove h)
        _ _ h3)).trans
      (ChamberSystem.reflTransGen_reductionStep_twoHomotopic h5)
  have hclosed₂ : galleryEnd x γ₂ = x :=
    (ChamberSystem.TwoHomotopic.galleryEnd_eq hTwo).symm.trans hclosed
  have hstrict : IsStrictGallery cs δ x γ₂ :=
    p9uDMB_isStrictGallery_of_isOrdinary hB h4.1
  have hdist := IsStrictGallery.dist_eq hB hstrict h4.2
  have hprod : cs.wordProd (galleryType γ₂) = 1 := by
    rw [← hdist, hclosed₂, hB.eq_one_self x]
  have hlen : (galleryType γ₂).length = 0 := by
    rw [← h4.2.eq, hprod, cs.length_one]
  have hnil : γ₂ = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using hlen
  rwa [hnil] at hTwo

end CFSG.ClassicalInvolution.Phan.PhanE

end
