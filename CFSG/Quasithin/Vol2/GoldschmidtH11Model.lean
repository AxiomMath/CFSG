module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Vol2.GoldschmidtH11Base

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [CharP F 2] (a : ℕ)

abbrev HV (F : Type) [Field F] [CharP F 2] (a : ℕ) : Type := ↥(hermSub a (Fin 2) F)

@[expose] def hm (v : HV F a) : Matrix (Fin 2) (Fin 2) F := Multiplicative.toAdd v.1

@[expose] def mkHV (M : Matrix (Fin 2) (Fin 2) F) (h : (frobPow a M)ᵀ = M) : HV F a :=
  ⟨Multiplicative.ofAdd M, h⟩

theorem hm_mul {v w : HV F a} : hm a (v * w) = hm a v + hm a w := rfl

theorem hm_one : hm a (1 : HV F a) = 0 := rfl

theorem hm_inv (v : HV F a) : hm a v⁻¹ = - hm a v := rfl

theorem hm_herm (v : HV F a) : (frobPow a (hm a v))ᵀ = hm a v := v.2

theorem hm_injective : Function.Injective (hm a : HV F a → Matrix (Fin 2) (Fin 2) F) :=
  fun _ _ h => Subtype.ext (Multiplicative.toAdd.injective h)

theorem hm_eq_iff {v w : HV F a} : hm a v = hm a w ↔ v = w := (hm_injective a).eq_iff

theorem hm_entry (v : HV F a) (i j : Fin 2) : sg a (hm a v j i) = hm a v i j := by
  have := congrFun (congrFun (hm_herm a v) i) j
  simpa [frobPow, sg_apply] using this

theorem frobPow_eq (X : Matrix (Fin 2) (Fin 2) F) : frobPow a X = X.map (sg a) := rfl

theorem frobPow_apply (X : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    frobPow a X i j = sg a (X i j) := rfl

variable [Finite F]

theorem frobPow_frobPow (h : Nat.card F = 2 ^ (2 * a)) (X : Matrix (Fin 2) (Fin 2) F) :
    frobPow a (frobPow a X) = X := by
  ext i j
  simp only [frobPow_apply, sg_sg a h]

omit [Finite F] in
theorem frobPow_mul (X Y : Matrix (Fin 2) (Fin 2) F) :
    frobPow a (X * Y) = frobPow a X * frobPow a Y := by
  simp only [frobPow_eq]; exact Matrix.map_mul

omit [Finite F] in
theorem frobPow_transpose (X : Matrix (Fin 2) (Fin 2) F) :
    frobPow a Xᵀ = (frobPow a X)ᵀ := by
  simp only [frobPow_eq]; exact Matrix.transpose_map

@[expose] def tw (γ : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  (γ : Matrix (Fin 2) (Fin 2) F) * X * (frobPow a (γ : Matrix (Fin 2) (Fin 2) F))ᵀ

omit [CharP F 2] [Finite F] in
theorem tw_add (γ : SL(2, F)) (X Y : Matrix (Fin 2) (Fin 2) F) :
    tw a γ (X + Y) = tw a γ X + tw a γ Y := by
  simp only [tw, Matrix.mul_add, Matrix.add_mul]

omit [Finite F] in
theorem tw_one (X : Matrix (Fin 2) (Fin 2) F) : tw a 1 X = X := by
  have : frobPow a (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
    ext i j; simp [frobPow_apply, Matrix.one_apply]
  simp [tw, this]

omit [Finite F] in
theorem tw_mul (γ δ : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    tw a (γ * δ) X = tw a γ (tw a δ X) := by
  simp only [tw, Matrix.SpecialLinearGroup.coe_mul, frobPow_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]

theorem tw_herm (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F)
    (hX : (frobPow a X)ᵀ = X) : (frobPow a (tw a γ X))ᵀ = tw a γ X := by
  have e1 : frobPow a ((γ : Matrix (Fin 2) (Fin 2) F) * X *
      (frobPow a (γ : Matrix (Fin 2) (Fin 2) F))ᵀ) =
      frobPow a γ * frobPow a X * (γ : Matrix (Fin 2) (Fin 2) F)ᵀ := by
    rw [frobPow_mul, frobPow_mul, frobPow_transpose, frobPow_frobPow a h]
  rw [tw, e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX]
  simp [Matrix.mul_assoc]

@[expose] def actFun (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) (v : HV F a) : HV F a :=
  mkHV a (tw a γ (hm a v)) (tw_herm a h γ _ (hm_herm a v))

theorem hm_actFun (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) (v : HV F a) :
    hm a (actFun a h γ v) = tw a γ (hm a v) := rfl

theorem actFun_mul_left (h : Nat.card F = 2 ^ (2 * a)) (γ δ : SL(2, F)) (v : HV F a) :
    actFun a h (γ * δ) v = actFun a h γ (actFun a h δ v) :=
  hm_injective a (by simp only [hm_actFun, tw_mul])

theorem actFun_one (h : Nat.card F = 2 ^ (2 * a)) (v : HV F a) : actFun a h 1 v = v :=
  hm_injective a (by simp only [hm_actFun, tw_one])

theorem actFun_map_mul (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) (v w : HV F a) :
    actFun a h γ (v * w) = actFun a h γ v * actFun a h γ w :=
  hm_injective a (by simp only [hm_actFun, hm_mul, tw_add])

@[expose] def actHom (h : Nat.card F = 2 ^ (2 * a)) : SL(2, F) →* MulAut (HV F a) where
  toFun γ :=
    { toFun := actFun a h γ
      invFun := actFun a h γ⁻¹
      left_inv := fun v => by rw [← actFun_mul_left, inv_mul_cancel, actFun_one]
      right_inv := fun v => by rw [← actFun_mul_left, mul_inv_cancel, actFun_one]
      map_mul' := actFun_map_mul a h γ }
  map_one' := MulEquiv.ext (actFun_one a h)
  map_mul' γ δ := MulEquiv.ext (actFun_mul_left a h γ δ)

theorem hm_actHom (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) (v : HV F a) :
    hm a (actHom a h γ v) = (γ : Matrix (Fin 2) (Fin 2) F) * hm a v *
      (frobPow a (γ : Matrix (Fin 2) (Fin 2) F))ᵀ := rfl

end CFSG.Quasithin.H11
