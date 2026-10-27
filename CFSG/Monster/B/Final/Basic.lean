module

public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.Pinned.GeneratorDeterminants

public section

namespace CFSG.Monster.B

open Matrix CFSG.Blueprint

abbrev Sbp : Type := Cbarᵐᵒᵖ

instance :
    IsSimpleGroup Sbp :=
  haveI := short_centralizer_generated_quotient_simple.2.2.1
  (MulEquiv.inv' Cbar).symm.isSimpleGroup

@[expose] noncomputable def betaRow (β : Cbar →* GL (Fin 4370) (ZMod 2)) :
    Sbp →* (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ where
  toFun s :=
    ⟨((β s.unop : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2))ᵀ,
      (((β s.unop)⁻¹ : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2))ᵀ,
      by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' s t := by
    apply Units.ext
    simp only [MulOpposite.unop_mul, map_mul, Units.val_mul, Matrix.transpose_mul]

theorem coe_betaRow (β : Cbar →* GL (Fin 4370) (ZMod 2)) (s : Sbp) :
    ((betaRow β s : (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      ((β s.unop : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2))ᵀ := rfl

theorem betaRow_injective {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : Function.Injective β) :
    Function.Injective (betaRow β) := by
  intro s t h
  have h' := congrArg (fun u : (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ =>
    (u : Matrix (Fin 4370) (Fin 4370) (ZMod 2))ᵀ) h
  simp only [coe_betaRow, Matrix.transpose_transpose] at h'
  exact MulOpposite.unop_injective (hβ (Units.ext h'))

theorem genA₁_mem :
    genA₁ ∈ NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2 :=
  Submonoid.subset_closure (Set.mem_insert _ _)

theorem genA₂_mem :
    genA₂ ∈ NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2 :=
  Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def bA₁ : NativeSporadic.B :=
  ⟨⟨genA₁, genA₁_mem⟩, ⟨genA₁, genA₁_mem⟩, Subtype.ext genA₁_mul_self, Subtype.ext genA₁_mul_self⟩

@[expose] noncomputable def bA₂ : NativeSporadic.B :=
  ⟨⟨genA₂, genA₂_mem⟩, ⟨genA₂ * genA₂, Submonoid.mul_mem _ genA₂_mem genA₂_mem⟩,
    Subtype.ext (by rw [Submonoid.coe_mul, ← Matrix.mul_assoc]; exact genA₂_cube),
    Subtype.ext (by rw [Submonoid.coe_mul]; exact genA₂_cube)⟩

@[expose] noncomputable def bMat : NativeSporadic.B →* Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2).subtype.comp
    (Units.coeHom _)

theorem bMat_injective : Function.Injective bMat := fun _ _ h => Units.ext (Subtype.ext h)

theorem bMat_bA₁ : bMat bA₁ = genA₁ := rfl

theorem bMat_bA₂ : bMat bA₂ = genA₂ := rfl

theorem bMat_bA₂_inv : bMat bA₂⁻¹ = genA₂ * genA₂ := by
  have h : bMat bA₂ * bMat bA₂⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [bMat_bA₂] at h
  calc bMat bA₂⁻¹ = (genA₂ * genA₂ * genA₂) * bMat bA₂⁻¹ := by rw [genA₂_cube, Matrix.one_mul]
    _ = genA₂ * genA₂ * (genA₂ * bMat bA₂⁻¹) := by simp only [Matrix.mul_assoc]
    _ = genA₂ * genA₂ := by rw [h, Matrix.mul_one]

end CFSG.Monster.B
