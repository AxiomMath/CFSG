module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

namespace CFSG
end CFSG
open CFSG

/-!
# Cardinality of `PGL₂` over a finite field

This module exposes the finite-field order formula independently of the
private copies used by the Bender--Suzuki development.
-/

noncomputable section

namespace CFSG.GorensteinWalter

/-- The order formula `|PGL₂(K)| = q(q² - 1)` for a finite field of order
`q = Nat.card K`. -/
public theorem pgl2_card_formula
    (K : Type*) [Field K] [Finite K] :
    Nat.card (PGL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let GL2 := Matrix.GeneralLinearGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalarInj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 ↦
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range =
          Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalarInj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 K := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card (PGL2 K) := by
    calc
      centerGL.index = mkPGL.ker.index := by
        rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card (PGL2 K) := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card (PGL2 K) =
        Nat.card (PGL2 K) * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) *
        (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) *
        (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

end CFSG.GorensteinWalter
