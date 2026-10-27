module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.SL3Natural
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

namespace Stellmacher.L3YC

section Scalar

variable {F : Type} [Field F] [Fintype F]

theorem end_scalar_of_commutes (hF : Fintype.card F = 2) (dual : Bool)
    (X : Matrix (Fin 3) (Fin 3) F)
    (hX : ∀ g ∈ StatedSL 3 F, moduleAct dual g * X = X * moduleAct dual g) :
    X = 0 ∨ X = 1 := by
  classical
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm
  let P : Matrix (Fin 3) (Fin 3) (ZMod 2) := X.map e
  have hgen : ∀ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 →
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * P = P * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro g hg
    set T : Matrix (Fin 3) (Fin 3) F := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).map e.symm with hT
    have hdet : T.det = 1 := by
      have h1 := RingHom.map_det e.symm.toRingHom (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
      rw [hg, map_one] at h1
      exact h1.symm
    have hTX : T * X = X * T := by
      cases dual with
      | false =>
        let g' : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero T (by
          rw [hdet]; exact one_ne_zero)
        have hmem : g' ∈ StatedSL 3 F := Subgroup.subset_closure hdet
        have := hX g' hmem
        simpa [moduleAct, g', Matrix.GeneralLinearGroup.mkOfDetNeZero] using this
      | true =>
        have hdetT : Tᵀ.det = 1 := by rw [Matrix.det_transpose]; exact hdet
        let g' : GL (Fin 3) F := (Matrix.GeneralLinearGroup.mkOfDetNeZero Tᵀ (by
          rw [hdetT]; exact one_ne_zero))⁻¹
        have hmem : g' ∈ StatedSL 3 F :=
          Subgroup.inv_mem _ (Subgroup.subset_closure hdetT)
        have := hX g' hmem
        simpa [moduleAct, g', Matrix.GeneralLinearGroup.mkOfDetNeZero] using this
    have h2 := congrArg (Matrix.map · e) hTX
    simp only [Matrix.map_mul] at h2
    have h3 : T.map e = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      rw [hT, Matrix.map_map]
      ext i j
      simp
    rwa [h3] at h2
  have hall : ∀ g ∈ CFSG.Open.StatedSL 3 (ZMod 2),
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * P = P * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro g hg
    unfold CFSG.Open.StatedSL at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one => simp
    | mul x y _ _ hx hy =>
      simp only [Units.val_mul]
      rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx =>
      exact (Commute.units_inv_left (show Commute (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) P from hx)).eq
  rcases CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.end_natural_scalar P hall
    with h | h
  · left
    exact Matrix.map_injective e.injective (h.trans (Matrix.map_zero _ (map_zero e)).symm)
  · right
    exact Matrix.map_injective e.injective (h.trans (Matrix.map_one _ (map_zero e) (map_one e)).symm)

end Scalar

end Stellmacher.L3YC

end CFSG.Quasithin
