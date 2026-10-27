
module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Monster.CodeAut.Perm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Monster.Code
open scoped Matrix

@[expose] def golayC : Subgroup (G6.PermMod 24) :=
  AddSubgroup.toSubgroup (CFSG.Monster.Code.C.toAddSubgroup)

@[expose] def unitVec (x : Fin 24) : G6.PermMod 24 :=
  Multiplicative.ofAdd (Pi.single x 1)

@[expose] def pairVec (x y : Fin 24) : G6.PermMod 24 := unitVec x * unitVec y

@[expose] def pairKer (x y : Fin 24) : Subgroup (G6.PermMod 24) :=
  AddSubgroup.toSubgroup (AddMonoidHom.ker
    (Pi.evalAddMonoidHom (fun _ : Fin 24 => ZMod 2) x +
      Pi.evalAddMonoidHom (fun _ : Fin 24 => ZMod 2) y))

@[expose] def permSubAct (Γ : Subgroup (Equiv.Perm (Fin 24))) (σ : ↥Γ) (x : G6.PermMod 24) :
    G6.PermMod 24 :=
  G6.permAct 24 (σ : Equiv.Perm (Fin 24)) x

@[expose] def m24Fix (e : G6.PermMod 24) : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | σ ∈ CFSG.Monster.Code.AutPerm ∧ G6.permAct 24 σ e = e}
  mul_mem' {σ τ} hσ hτ := ⟨CFSG.Monster.Code.AutPerm.mul_mem hσ.1 hτ.1, by
    rw [map_mul, MulAut.mul_apply, hτ.2, hσ.2]⟩
  one_mem' := ⟨CFSG.Monster.Code.AutPerm.one_mem, by simp⟩
  inv_mem' {σ} hσ := ⟨CFSG.Monster.Code.AutPerm.inv_mem hσ.1, by
    rw [map_inv]
    conv_lhs => rw [← hσ.2]
    simp⟩

@[expose] def FFModel.golaySec (Γ : Subgroup (Equiv.Perm (Fin 24))) (numer denom : Subgroup (G6.PermMod 24)) :
    FFModel where
  Gam := ↥Γ
  Amb := G6.PermMod 24
  act := permSubAct Γ
  sec := numer
  ker := denom

section Mathieu

variable {V : Type*} [CommGroup V]

@[expose] def MathieuCode24 (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  (FFModel.golaySec CFSG.Monster.Code.AutPerm golayC (Subgroup.zpowers (G6.allOnes 24))).Realizes H U Z

@[expose] def MathieuCocode24 (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  (FFModel.golaySec CFSG.Monster.Code.AutPerm (G6.coreMod 24) golayC).Realizes H U Z

@[expose] def MathieuCode23 (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ x : Fin 24, (FFModel.golaySec (CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x)
    golayC (Subgroup.zpowers (G6.allOnes 24))).Realizes H U Z

@[expose] def MathieuCocode23 (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ x : Fin 24, (FFModel.golaySec (CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x)
    (G6.coreMod 24) golayC).Realizes H U Z

@[expose] def MathieuCode22 (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ x y : Fin 24, x ≠ y ∧
    (FFModel.golaySec (CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) (golayC ⊓ pairKer x y)
      (Subgroup.zpowers (G6.allOnes 24))).Realizes H U Z

@[expose] def MathieuCocode22 (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ x y : Fin 24, x ≠ y ∧
    (FFModel.golaySec (CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) (G6.coreMod 24)
      (golayC ⊔ Subgroup.zpowers (pairVec x y))).Realizes H U Z

@[expose] def M12Ten (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ eY : G6.PermMod 24, eY ∈ golayC ∧ hammingNorm (Multiplicative.toAdd eY) = 12 ∧
    (FFModel.golaySec (m24Fix eY) golayC
      (Subgroup.closure {G6.allOnes 24, eY})).Realizes H U Z

end Mathieu

section TwelveDim

variable {V : Type*} [CommGroup V]

@[expose] def Mhat22Twelve (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (Γ₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 6) K)),
      Nat.card K = 4 ∧ IsHat ↥Γ₀ ↥quasithinM22 ∧
      (∃ B : Matrix (Fin 6) (Fin 6) K, B.det ≠ 0 ∧ (frobPow 1 B)ᵀ = B ∧
        ∀ g ∈ Γ₀, (frobPow 1 ((g : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))ᵀ * B *
          ((g : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = B) ∧
      (FFModel.nat Γ₀).Realizes H U Z

@[expose] def J2Twelve (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K)
    (Γ₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)),
    Nat.card K = 4 ∧ Γ₀ ≤ quasithinG2 K ∧ (FFModel.zornQ Γ₀).Realizes H U Z

end TwelveDim

end CFSG.Quasithin
