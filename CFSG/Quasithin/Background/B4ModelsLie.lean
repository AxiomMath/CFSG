
module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Matrix

section G2

variable {F : Type} [Field F]

@[expose] def zornO0 (F : Type) [Field F] : Subgroup (Multiplicative (quasithinZorn F)) :=
  AddSubgroup.toSubgroup
    { carrier := {x : quasithinZorn F | x.1 + x.2.2.2 = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at hx hy ⊢
        rw [add_add_add_comm, hx, hy, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg] at hx ⊢
        rw [← neg_add, hx, neg_zero] }

@[expose] def zornR (F : Type) [Field F] : Subgroup (Multiplicative (quasithinZorn F)) :=
  AddSubgroup.toSubgroup
    { carrier := {x : quasithinZorn F | ∃ c : F, x = (c, 0, 0, c)}
      add_mem' := fun {x y} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨c + d, by rw [hc, hd]; ext <;> simp⟩
      zero_mem' := ⟨0, rfl⟩
      neg_mem' := fun {x} ⟨c, hc⟩ => ⟨-c, by rw [hc]; simp [Prod.neg_mk]⟩ }

@[expose] def zornAct (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)) (g : ↥Γ)
    (x : Multiplicative (quasithinZorn F)) : Multiplicative (quasithinZorn F) :=
  Multiplicative.ofAdd ((g : quasithinZorn F ≃ₗ[F] quasithinZorn F) (Multiplicative.toAdd x))

@[expose] def FFModel.zornQ (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)) : FFModel where
  Gam := ↥Γ
  Amb := Multiplicative (quasithinZorn F)
  act := zornAct Γ
  sec := zornO0 F
  ker := zornR F

end G2

section G2Pred

variable {V : Type*} [CommGroup V]

@[expose] def G2Natural (H : Subgroup (MulAut V)) (U Z : Subgroup V) (a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.zornQ (quasithinG2 K)).Realizes H U Z

@[expose] def G2NaturalDerived (H : Subgroup (MulAut V)) (U Z : Subgroup V) (a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes H U Z

end G2Pred

section ExteriorModel

variable (K : Type) [Field K]

@[expose] noncomputable def extSqAct (d : ℕ) (g : ↥(StatedSL d K))
    (x : Multiplicative (⋀[K]^2 (Fin d → K))) : Multiplicative (⋀[K]^2 (Fin d → K)) :=
  Multiplicative.ofAdd (exteriorPower.map 2
    (Matrix.toLin' (((g : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)))
    (Multiplicative.toAdd x))

@[expose] noncomputable def FFModel.extSq (d : ℕ) : FFModel where
  Gam := ↥(StatedSL d K)
  Amb := Multiplicative (⋀[K]^2 (Fin d → K))
  act := extSqAct K d
  sec := ⊤
  ker := ⊥

end ExteriorModel

section Exterior

variable {V : Type*} [CommGroup V]

@[expose] noncomputable def SLExteriorTwo (H : Subgroup (MulAut V)) (U Z : Subgroup V) (d : ℕ) : Prop :=
  (FFModel.extSq (ZMod 2) d).Realizes H U Z

end Exterior

section Twisted

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def frobPow (a : ℕ) (X : Matrix ι ι F) : Matrix ι ι F := X.map fun x => x ^ 2 ^ a

@[expose] def hermSub (a : ℕ) (ι : Type) [Fintype ι] (F : Type) [Field F] [CharP F 2] :
    Subgroup (Multiplicative (Matrix ι ι F)) :=
  AddSubgroup.toSubgroup
    { carrier := {X : Matrix ι ι F | (frobPow a X)ᵀ = X}
      add_mem' := fun {X Y} hX hY => by
        simp only [Set.mem_ofPred_eq] at hX hY ⊢
        have : frobPow a (X + Y) = frobPow a X + frobPow a Y := by
          ext i j
          simp only [frobPow, Matrix.map_apply, Matrix.add_apply]
          exact add_pow_char_pow _ _ 2 a
        rw [this, Matrix.transpose_add, hX, hY]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        ext i j
        simp [frobPow]
      neg_mem' := fun {X} hX => by
        simp only [Set.mem_ofPred_eq] at hX ⊢
        have : frobPow a (-X) = -frobPow a X := by
          ext i j
          simp only [frobPow, Matrix.map_apply, Matrix.neg_apply]
          have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
          have hneg : ∀ y : F, -y = y := fun y => by
            have : y + y = 0 := by rw [← two_mul, h2, zero_mul]
            exact neg_eq_of_add_eq_zero_right this
          rw [hneg, hneg]
        rw [this, Matrix.transpose_neg, hX] }

@[expose] def twistAct (a : ℕ) (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) (g : ↥Γ)
    (X : Multiplicative (Matrix ι ι F)) : Multiplicative (Matrix ι ι F) :=
  Multiplicative.ofAdd
    (((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) * Multiplicative.toAdd X *
      (frobPow a ((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F))ᵀ)

@[expose] def FFModel.twistTensor [CharP F 2] (a : ℕ) (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) :
    FFModel where
  Gam := ↥Γ
  Amb := Multiplicative (Matrix ι ι F)
  act := twistAct a Γ
  sec := hermSub a ι F
  ker := ⊥

end Twisted

section TwistedPred

variable {V : Type*} [CommGroup V]

@[expose] def TwistedTensorSL (H : Subgroup (MulAut V)) (U Z : Subgroup V) (d a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ (2 * a) ∧
    (FFModel.twistTensor a (StatedSL d K)).Realizes H U Z

@[expose] def TwistedTensorSp4 (H : Subgroup (MulAut V)) (U Z : Subgroup V) (a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ (2 * a) ∧
    (FFModel.twistTensor a (StatedSp 2 K)).Realizes H U Z

@[expose] def BinaryNineTensor (H : Subgroup (MulAut V)) (U Z : Subgroup V) (a : ℕ) : Prop :=
  TwistedTensorSL H U Z 3 a

@[expose] def BinaryOrthogonalFour (H : Subgroup (MulAut V)) (U Z : Subgroup V) (a : ℕ) : Prop :=
  TwistedTensorSL H U Z 2 a

end TwistedPred

end CFSG.Quasithin
