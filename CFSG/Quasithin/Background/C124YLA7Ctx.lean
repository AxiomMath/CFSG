module

public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Base

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A7

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique.L246.C123

abbrev Q7 : Type := Multiplicative (Fin 4 → ZMod 2)

variable (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))

@[expose] noncomputable def rhoA : A7 →* MulAut Q7 where
  toFun σ :=
    { toFun := a7Act α σ
      invFun := a7Act α σ⁻¹
      left_inv := fun q => by rw [← a7Act_mul_act, inv_mul_cancel, a7Act_one]
      right_inv := fun q => by rw [← a7Act_mul_act, mul_inv_cancel, a7Act_one]
      map_mul' := a7Act_mul α σ }
  map_one' := MulEquiv.ext (a7Act_one α)
  map_mul' σ τ := MulEquiv.ext (a7Act_mul_act α σ τ)

theorem altLift7_inj : Function.Injective altLift7 := fun _ _ h =>
  Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective _ (congrArg Subtype.val h))

theorem rhoA_injective : Function.Injective (rhoA α) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  have h1 : rhoA α σ = 1 := hσ
  have h2 : ∀ y : Fin 4 → ZMod 2,
      ((α (altLift7 σ) : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec y = y := fun y => by
    have := congrArg (fun f : MulAut Q7 => Multiplicative.toAdd (f (Multiplicative.ofAdd y))) h1
    exact this
  have h3 : α (altLift7 σ) = 1 := by
    apply Units.ext
    ext i j
    have := congrFun (h2 (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have h4 : altLift7 σ = 1 := α.injective (by rw [h3, map_one])
  exact Subgroup.mem_bot.2 (altLift7_inj (by rw [h4, map_one]))

theorem card_Q7 : Nat.card Q7 = 16 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp

theorem sq_Q7 (q : Q7) : q ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  ext i
  simp only [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply, nsmul_eq_mul]
  have : ∀ x : ZMod 2, (2 : ZMod 2) * x = 0 := by decide
  simpa using this _

structure A7Ctx {W : Type*} [CommGroup W] (Ls : Subgroup (MulAut W)) (U Z : Subgroup W) where
  α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)
  π : A7 →* ↥Ls
  real : (FFModel.a7Four α).RealizesVia Ls U Z π

end CFSG.Quasithin.C124.YL.A7
