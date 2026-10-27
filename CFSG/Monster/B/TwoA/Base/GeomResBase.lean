
module

public import CFSG.Monster.B.TwoA.Base.GeomObjBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

attribute [local instance] parAction

@[expose] def parRes (F : Set ParGeom) : Set ParGeom :=
  {x | parType x ∉ parType '' F ∧ ∀ y ∈ F, parInc x y}

theorem smul_mem_parRes {g : Shat} {F : Set ParGeom} {x : ParGeom} (hx : x ∈ parRes F) :
    g • x ∈ parRes ((g • ·) '' F) := by
  refine ⟨by rw [parType_image_smul, parType_smul]; exact hx.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (parInc_smul_iff g x y).2 (hx.2 y hy)

theorem parRes_smul (g : Shat) (F : Set ParGeom) :
    parRes ((g • ·) '' F) = (g • ·) '' parRes F := by
  refine Set.eq_of_subset_of_subset (fun x hx => ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩) ?_
  · have h := smul_mem_parRes (g := g⁻¹) hx
    rwa [Set.image_image, show (fun y => g⁻¹ • g • y) = id from funext fun y => inv_smul_smul g y,
      Set.image_id] at h
  · rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_parRes hx

@[expose] def stdSub (J : Set ℕ) : Set ParGeom := {x | x ∈ stdParFlag ∧ parType x ∈ J}

theorem isParFlag_stdSub (J : Set ℕ) : IsParFlag (stdSub J) :=
  fun x hx y hy => stdParFlag_isParFlag.1 x hx.1 y hy.1

theorem parType_stdSub (J : Set ℕ) (hJ : J ⊆ Set.Icc 1 5) : parType '' stdSub J = J := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.2
  · intro hs
    obtain ⟨h1, h5⟩ := hJ hs
    exact ⟨stdObj s h1 h5, ⟨rfl, hs⟩, rfl⟩

@[expose] def resTransport (g : Shat) (F : Set ParGeom) (j : ℕ) :
    {x : ParGeom // x ∈ parRes F ∧ parType x = j} ≃
      {x : ParGeom // x ∈ parRes ((g • ·) '' F) ∧ parType x = j} where
  toFun x := ⟨g • x.1, smul_mem_parRes x.2.1, by rw [parType_smul]; exact x.2.2⟩
  invFun y := ⟨g⁻¹ • y.1, by
      have h := smul_mem_parRes (g := g⁻¹) y.2.1
      rwa [Set.image_image, show (fun z => g⁻¹ • g • z) = id from
        funext fun z => inv_smul_smul g z, Set.image_id] at h, by
      rw [parType_smul]; exact y.2.2⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.1)
  right_inv y := Subtype.ext (smul_inv_smul g y.1)

theorem coe_resTransport (g : Shat) (F : Set ParGeom) (j : ℕ)
    (x : {x : ParGeom // x ∈ parRes F ∧ parType x = j}) :
    ((resTransport g F j x).1.1.2) = conjSub (g : Dfull) x.1.1.2 := rfl

end CFSG.Monster.B.TwoA
