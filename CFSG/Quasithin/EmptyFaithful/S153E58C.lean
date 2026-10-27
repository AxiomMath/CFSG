module

public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Quasithin.EmptyFaithful.S153E59C
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace S153E58

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev V3 : Type := Multiplicative (Fin 3 → ZMod 2)

section Transvections

theorem transv_sq : ∀ x φ : Fin 3 → ZMod 2, φ ⬝ᵥ x = 0 →
    ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + vecMulVec x φ) *
      ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + vecMulVec x φ) = 1 := by
  decide

@[expose] def transvGL (x φ : Fin 3 → ZMod 2) (h : φ ⬝ᵥ x = 0) : GL (Fin 3) (ZMod 2) :=
  ⟨1 + vecMulVec x φ, 1 + vecMulVec x φ, transv_sq x φ h, transv_sq x φ h⟩

theorem transvGL_mulVec (x φ : Fin 3 → ZMod 2) (h : φ ⬝ᵥ x = 0) (v : Fin 3 → ZMod 2) :
    ((transvGL x φ h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v =
      v + (φ ⬝ᵥ v) • x := by
  change ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + vecMulVec x φ) *ᵥ v = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  simp

theorem key_form : ∀ v x : Fin 3 → ZMod 2, x ≠ 0 →
    ∃ φ w : Fin 3 → ZMod 2, φ ⬝ᵥ x = 0 ∧ φ ⬝ᵥ v = 0 ∧ φ ⬝ᵥ w = 1 := by
  decide

theorem key_schur : ∀ x : Fin 3 → ZMod 2, x ≠ 0 →
    ∃ φ v : Fin 3 → ZMod 2, φ ⬝ᵥ x = 0 ∧ φ ⬝ᵥ v = 1 := by
  decide

theorem zmod_two_eq (z : ZMod 2) (h : z ≠ 0) : z = 1 := by
  revert z; decide

theorem mem_statedSL_three_two (g : GL (Fin 3) (ZMod 2)) : g ∈ StatedSL 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

@[expose] def transvSL (x φ : Fin 3 → ZMod 2) (h : φ ⬝ᵥ x = 0) : ↥(StatedSL 3 (ZMod 2)) :=
  ⟨transvGL x φ h, mem_statedSL_three_two _⟩

end Transvections

section AutGL

theorem nonempty_mulEquiv_pi_of_sq_eq_one {W : Type*} [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) {d : ℕ} (hcard : Nat.card W = 2 ^ d) :
    Nonempty (W ≃* Multiplicative (Fin d → ZMod 2)) := by
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule fun a => by
    change Additive.ofMul ((Additive.toMul a) ^ 2) = 0
    rw [h2]
    rfl
  have hfin : Module.finrank (ZMod 2) (Additive W) = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at h
    have hW : Nat.card (Additive W) = Nat.card W := rfl
    rw [hW, hcard] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hfin' : Module.finrank (ZMod 2) (Additive W) =
      Module.finrank (ZMod 2) (Fin d → ZMod 2) := by
    rw [hfin, Module.finrank_fin_fun]
  exact ⟨AddEquiv.toMultiplicativeRight (LinearEquiv.ofFinrankEq _ _ hfin').toAddEquiv⟩

@[expose] noncomputable def mulAutPiEquivLinearEquiv (d : ℕ) :
    MulAut (Multiplicative (Fin d → ZMod 2)) ≃*
      ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) where
  toFun φ :=
    { ((AddEquiv.toMultiplicative.symm φ :
          (Fin d → ZMod 2) ≃+ (Fin d → ZMod 2)).toAddMonoidHom.toZModLinearMap 2) with
      invFun := (AddEquiv.toMultiplicative.symm φ : (Fin d → ZMod 2) ≃+ (Fin d → ZMod 2)).symm
      left_inv :=
        (AddEquiv.toMultiplicative.symm φ : (Fin d → ZMod 2) ≃+ (Fin d → ZMod 2)).left_inv
      right_inv :=
        (AddEquiv.toMultiplicative.symm φ : (Fin d → ZMod 2) ≃+ (Fin d → ZMod 2)).right_inv }
  invFun ψ := AddEquiv.toMultiplicative ψ.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def mulAutPiEquivGL (d : ℕ) :
    MulAut (Multiplicative (Fin d → ZMod 2)) ≃* GL (Fin d) (ZMod 2) :=
  (mulAutPiEquivLinearEquiv d).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin d → ZMod 2)).symm.trans
      (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := ZMod 2)).symm)

theorem mulAutPiEquivGL_symm_apply (d : ℕ) (γ : GL (Fin d) (ZMod 2))
    (x : Multiplicative (Fin d → ZMod 2)) :
    (mulAutPiEquivGL d).symm γ x =
      Multiplicative.ofAdd ((γ : Matrix (Fin d) (Fin d) (ZMod 2)).mulVec
        (Multiplicative.toAdd x)) := by
  simp [mulAutPiEquivGL, mulAutPiEquivLinearEquiv, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem card_statedSL_three_two : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Quasithin.S153E59.card_statedSL_three_two

theorem card_mulAut_statedSL_three_two : Nat.card (MulAut ↥(StatedSL 3 (ZMod 2))) = 336 :=
  CFSG.Quasithin.S153E59.card_mulAut_statedSL_three_two

theorem isSimpleGroup_statedSL_three_two : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
  CFSG.Quasithin.S153E59.isSimpleGroup_statedSL_three_two

theorem statedSL_center {s : ↥(StatedSL 3 (ZMod 2))} (hs : ∀ t, s * t = t * s) : s = 1 :=
  CFSG.Quasithin.S153E59.statedSL_center hs

end AutGL

end S153E58

end CFSG.Quasithin
