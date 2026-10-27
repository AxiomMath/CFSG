module

public import CFSG.LocalAnalysis.StandardType.FS81.Realized

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

theorem vec_injective (B : Basis3 G k) : Function.Injective B.vec := by
  intro e e' h
  have h1 : B.vec (e - e') = 1 := by
    have h2 := B.vec_add (e - e') e'
    rw [sub_add_cancel, h] at h2
    exact (mul_eq_right.mp h2.symm)
  exact sub_eq_zero.mp (B.indep _ h1)

theorem coords_vec (B : Basis3 G k) (e : Coords k) :
    B.coords ⟨B.vec e, B.vec_mem_span e⟩ = e :=
  B.vec_injective (B.vec_coords _)

theorem coords_injective (B : Basis3 G k) : Function.Injective B.coords := by
  intro y z h
  apply Subtype.ext
  rw [← B.vec_coords y, ← B.vec_coords z, h]

theorem coords_mul (B : Basis3 G k) (y z : ↥B.span) :
    B.coords (y * z) = B.coords y + B.coords z := by
  apply B.vec_injective
  rw [B.vec_coords, B.vec_add, B.vec_coords, B.vec_coords]
  rfl

theorem coords_bS (B : Basis3 G k) (j : Fin k) : B.coords (B.bS j) = Pi.single j 1 := by
  apply B.vec_injective
  rw [B.vec_coords, B.vec_single]
  rfl

@[expose] noncomputable def equiv (B : Basis3 G k) : Multiplicative (Coords k) ≃* ↥B.span where
  toFun e := ⟨B.vec (Multiplicative.toAdd e), B.vec_mem_span _⟩
  invFun y := Multiplicative.ofAdd (B.coords y)
  left_inv e := by
    show Multiplicative.ofAdd (B.coords ⟨B.vec (Multiplicative.toAdd e), _⟩) = e
    rw [B.coords_vec]
    rfl
  right_inv y := Subtype.ext (B.vec_coords y)
  map_mul' e e' := Subtype.ext (B.vec_add _ _)

@[expose] noncomputable def linOf (B : Basis3 G k) (φ : MulAut ↥B.span) :
    Coords k →ₗ[ZMod 3] Coords k :=
  AddMonoidHom.toZModLinearMap 3
    (MonoidHom.toAdditive ((B.equiv.symm.toMonoidHom.comp φ.toMonoidHom).comp
      B.equiv.toMonoidHom))

theorem linOf_apply (B : Basis3 G k) (φ : MulAut ↥B.span) (e : Coords k) :
    B.linOf φ e = B.coords (φ ⟨B.vec e, B.vec_mem_span e⟩) :=
  rfl

theorem linOf_single (B : Basis3 G k) (φ : MulAut ↥B.span) (j : Fin k) :
    B.linOf φ (Pi.single j 1) = fun i => B.matOf φ i j := by
  rw [linOf_apply]
  have : (⟨B.vec (Pi.single j 1), B.vec_mem_span _⟩ : ↥B.span) = B.bS j :=
    Subtype.ext (B.vec_single j)
  rw [this]
  funext i
  rw [matOf_apply]

theorem linOf_eq_toLin' (B : Basis3 G k) (φ : MulAut ↥B.span) :
    B.linOf φ = Matrix.toLin' (B.matOf φ) := by
  refine (Pi.basisFun (ZMod 3) (Fin k)).ext fun j => ?_
  rw [Pi.basisFun_apply, linOf_single, Matrix.toLin'_apply]
  funext i
  simp [Matrix.mulVec_single]

theorem coords_apply_vec (B : Basis3 G k) (φ : MulAut ↥B.span) (e : Coords k) :
    B.coords (φ ⟨B.vec e, B.vec_mem_span e⟩) = B.matOf φ *ᵥ e := by
  rw [← linOf_apply, linOf_eq_toLin', Matrix.toLin'_apply]

theorem coords_apply (B : Basis3 G k) (φ : MulAut ↥B.span) (y : ↥B.span) :
    B.coords (φ y) = B.matOf φ *ᵥ B.coords y := by
  have hy : y = ⟨B.vec (B.coords y), B.vec_mem_span _⟩ := Subtype.ext (B.vec_coords y).symm
  conv_lhs => rw [hy]
  exact B.coords_apply_vec φ _

theorem matOf_mul (B : Basis3 G k) (φ ψ : MulAut ↥B.span) :
    B.matOf (φ * ψ) = B.matOf φ * B.matOf ψ := by
  apply Matrix.toLin'.injective
  refine (Pi.basisFun (ZMod 3) (Fin k)).ext fun j => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Pi.basisFun_apply, ← Matrix.mulVec_mulVec]
  rw [← coords_apply_vec, MulAut.mul_apply, coords_apply, coords_apply_vec]

theorem matOf_one (B : Basis3 G k) : B.matOf 1 = 1 := by
  ext i j
  rw [matOf_apply, MulAut.one_apply, coords_bS, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, if_neg h]

theorem matOf_injective (B : Basis3 G k) : Function.Injective B.matOf := by
  intro φ ψ h
  refine MulEquiv.ext fun y => B.coords_injective ?_
  rw [coords_apply, coords_apply, h]

@[expose] noncomputable def matHom (B : Basis3 G k) :
    MulAut ↥B.span →* Matrix (Fin k) (Fin k) (ZMod 3) where
  toFun := B.matOf
  map_one' := B.matOf_one
  map_mul' := B.matOf_mul

@[expose] noncomputable def glHom (B : Basis3 G k) :
    MulAut ↥B.span →* GL (Fin k) (ZMod 3) :=
  B.matHom.toHomUnits

theorem coe_glHom (B : Basis3 G k) (φ : MulAut ↥B.span) :
    ((B.glHom φ : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) = B.matOf φ :=
  rfl

theorem glHom_injective (B : Basis3 G k) : Function.Injective B.glHom := fun φ ψ h =>
  B.matOf_injective (by rw [← coe_glHom, ← coe_glHom, h])

theorem matOf_eq_of_acts (B : Basis3 G k) {φ : MulAut ↥B.span} {g : G}
    (hφ : ∀ y : ↥B.span, ((φ y : ↥B.span) : G) = g * y * g⁻¹)
    {A : Matrix (Fin k) (Fin k) (ZMod 3)} (hA : B.Acts g A) : B.matOf φ = A := by
  ext i j
  rw [matOf_apply]
  have : φ (B.bS j) = ⟨B.vec (fun i => A i j), B.vec_mem_span _⟩ := by
    apply Subtype.ext
    rw [hφ]
    exact hA j
  rw [this, coords_vec]

theorem acts_matOf (B : Basis3 G k) {φ : MulAut ↥B.span} {g : G}
    (hφ : ∀ y : ↥B.span, ((φ y : ↥B.span) : G) = g * y * g⁻¹) : B.Acts g (B.matOf φ) := by
  intro j
  have : (fun i => B.matOf φ i j) = B.coords (φ (B.bS j)) := by
    funext i
    rw [matOf_apply]
  rw [this, B.vec_coords, hφ]
  rfl

theorem mem_realized_iff [Finite G] (B : Basis3 G k) (H : Subgroup G)
    (A : Matrix (Fin k) (Fin k) (ZMod 3)) :
    A ∈ B.realized H ↔ ∃ φ ∈ ggInduced H B.span, B.matOf φ = A := by
  constructor
  · rintro ⟨g, hgH, hg⟩
    have hgN := B.mem_normalizer_of_acts hg
    refine ⟨B.span.normalizerMonoidHom ⟨g, hgN⟩, ⟨g, hgH, hgN, fun y => ?_⟩, ?_⟩
    · exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    · exact B.matOf_eq_of_acts (fun y => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _) hg
  · rintro ⟨φ, ⟨g, hgH, -, hφ⟩, rfl⟩
    exact ⟨g, hgH, B.acts_matOf hφ⟩

end Basis3

end CFSG.StandardType.FrameRoute.FS81

end
