module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4aW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4aT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H

private abbrev s16h_e3_o4atwIota : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem s16h_e3_o4atw_quad_zero {K : Type} [Field K] {b c : K} :
    StatedQuadMinus 2 K b c (0 : s16h_e3_o4atwIota → K) = 0 := by
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]

private theorem s16h_e3_o4atw_toAddMap_scalar {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (ω : K) (hω : ω ≠ 0) (x : ι → K) :
    toAddMap (natAut (StatedScalars ι K)
      ⟨Matrix.GeneralLinearGroup.scalar ι (Units.mk0 ω hω),
        ⟨Units.mk0 ω hω, rfl⟩⟩) x = ω • x := by
  rw [toAddMap_natAut, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem s16h_H5O4a_cover_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ z ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), z ≠ 1 ∧ z ^ 3 = 1 ∧
      ∀ v : StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K, v ≠ 1 →
        ∃ h ∈ natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)),
          ∃ mu ∈ natImage (StatedScalars (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K),
            (h * z * h⁻¹) v = mu v := by
  classical
  obtain ⟨z, hzΩ, hz1, hz3, ⟨e, he_ne, he_Q, ω, hω0, hz_e⟩, hfix⟩ :=
    s16h_H5O4a_torus (K := K) hK (b := b) (c := c)
  refine ⟨z, hzΩ, hz1, hz3, ?_⟩
  intro v hv
  have hv0 : Multiplicative.toAdd v ≠ 0 := fun h => hv ((toAdd_eq_zero).mp h)
  by_cases hQ0 : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) = 0
  ·
    obtain ⟨h, hh, hhe⟩ := s16h_H5O4a_witt (K := K) (b := b) (c := c) hirr (v := e)
      (w := Multiplicative.toAdd v) he_ne hv0 (by rw [hQ0, he_Q])
    let mu : MulAut (StdMod s16h_e3_o4atwIota K) :=
      natAut (StatedScalars s16h_e3_o4atwIota K)
        ⟨Matrix.GeneralLinearGroup.scalar s16h_e3_o4atwIota (Units.mk0 ω hω0),
          ⟨Units.mk0 ω hω0, rfl⟩⟩
    refine ⟨h, hh, mu, ?_, ?_⟩
    · exact ⟨⟨Matrix.GeneralLinearGroup.scalar s16h_e3_o4atwIota (Units.mk0 ω hω0),
        ⟨Units.mk0 ω hω0, rfl⟩⟩, rfl⟩
    · apply Multiplicative.ext
      show toAddMap (h * z * h⁻¹) (Multiplicative.toAdd v) =
        toAddMap mu (Multiplicative.toAdd v)
      rw [toAddMap_mul, toAddMap_mul]
      have h_inv : toAddMap h⁻¹ (Multiplicative.toAdd v) = e := by
        rw [← hhe, toAddMap_apply_inv]
      have hsmul : toAddMap h (ω • e) = ω • toAddMap h e := by
        obtain ⟨γ, rfl⟩ := hh
        exact isSemilinear_matAut (γ : GL s16h_e3_o4atwIota K) ω e
      rw [h_inv, hz_e, hsmul, hhe,
        s16h_e3_o4atw_toAddMap_scalar ω hω0 (Multiplicative.toAdd v)]
  ·
    obtain ⟨x, hxQ, hzx⟩ := hfix (StatedQuadMinus 2 K b c (Multiplicative.toAdd v)) hQ0
    have hx_ne : x ≠ 0 := by
      intro hx0
      apply hQ0
      rw [← hxQ, hx0]
      exact s16h_e3_o4atw_quad_zero
    obtain ⟨h, hh, hhx⟩ := s16h_H5O4a_witt (K := K) (b := b) (c := c) hirr (v := x)
      (w := Multiplicative.toAdd v) hx_ne hv0 hxQ.symm
    refine ⟨h, hh, 1, (natImage (StatedScalars s16h_e3_o4atwIota K)).one_mem, ?_⟩
    apply Multiplicative.ext
    show toAddMap (h * z * h⁻¹) (Multiplicative.toAdd v) =
      toAddMap (1 : MulAut (StdMod s16h_e3_o4atwIota K)) (Multiplicative.toAdd v)
    rw [toAddMap_mul, toAddMap_mul]
    have h_inv : toAddMap h⁻¹ (Multiplicative.toAdd v) = x := by
      rw [← hhx, toAddMap_apply_inv]
    rw [h_inv, hzx, hhx, toAddMap_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
