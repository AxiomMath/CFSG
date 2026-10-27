module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoExcDefs
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aPat

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar LevTwoType
open CFSG.LieType.RootSystem
open scoped Matrix

private theorem levTwoS3a_root_eq_E8 : LevTwoType.E8.root = Tag.cartan Tag.E8 := by
  rw [show LevTwoType.E8.root = (CartanMatrix.E 8)ᵀ from rfl]
  rw [show (CartanMatrix.E 8)ᵀ = CartanMatrix.E 8 from by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CartanMatrix.E]]
  rw [show Tag.cartan Tag.E8 = CartanMatrix.E 8 from by
    change Tag.cartanE 8 = CartanMatrix.E 8
    exact cartanE_eq 8]

private theorem levTwoS3a_root_eq_E7 : LevTwoType.E7.root = Tag.cartan Tag.E7 := by
  rw [show LevTwoType.E7.root = (CartanMatrix.E 7)ᵀ from rfl]
  rw [show (CartanMatrix.E 7)ᵀ = CartanMatrix.E 7 from by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CartanMatrix.E]]
  rw [show Tag.cartan Tag.E7 = CartanMatrix.E 7 from by
    change Tag.cartanE 7 = CartanMatrix.E 7
    exact cartanE_eq 7]

private theorem levTwoS3a_root_eq_E6 : LevTwoType.E6.root = Tag.cartan Tag.E6 := by
  rw [show LevTwoType.E6.root = (CartanMatrix.E 6)ᵀ from rfl]
  rw [show (CartanMatrix.E 6)ᵀ = CartanMatrix.E 6 from by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CartanMatrix.E]]
  rw [show Tag.cartan Tag.E6 = CartanMatrix.E 6 from by
    change Tag.cartanE 6 = CartanMatrix.E 6
    exact cartanE_eq 6]

private theorem levTwoS3a_root_eq_F4 : LevTwoType.F4.root = Tag.cartan Tag.F4 := by
  rw [show LevTwoType.F4.root = (CartanMatrix.F₄)ᵀ from rfl]
  rw [show (CartanMatrix.F₄)ᵀ = Tag.cartan Tag.F4 from by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]

theorem levTwoEngine_E8_of_finite
    (h : ExcFinite Tag.E8 kacE8) : LevTwoEngine LevTwoType.E8 := by
  intro p hp hp2 c Φ hdata
  have hdata' : LevTwoData (isFiniteType_cartan Tag.E8) p c Φ :=
    (levTwoS3a_data_congr levTwoS3a_root_eq_E8 LevTwoType.E8.rootFT
      (isFiniteType_cartan Tag.E8) p c Φ).1 hdata
  exact (levTwoS3a_tcRoot_congr levTwoS3a_root_eq_E8 LevTwoType.E8.rootFT
    (isFiniteType_cartan Tag.E8) Φ).2
    (levTwoS3a_engine_E8 h p hp hp2 c Φ hdata')

theorem levTwoEngine_E7_of_finite
    (h : ExcFinite Tag.E7 kacE7) : LevTwoEngine LevTwoType.E7 := by
  intro p hp hp2 c Φ hdata
  have hdata' : LevTwoData (isFiniteType_cartan Tag.E7) p c Φ :=
    (levTwoS3a_data_congr levTwoS3a_root_eq_E7 LevTwoType.E7.rootFT
      (isFiniteType_cartan Tag.E7) p c Φ).1 hdata
  exact (levTwoS3a_tcRoot_congr levTwoS3a_root_eq_E7 LevTwoType.E7.rootFT
    (isFiniteType_cartan Tag.E7) Φ).2
    (levTwoS3a_engine_E7 h p hp hp2 c Φ hdata')

theorem levTwoEngine_E6_of_finite
    (h : ExcFinite Tag.E6 kacE6) : LevTwoEngine LevTwoType.E6 := by
  intro p hp hp2 c Φ hdata
  have hdata' : LevTwoData (isFiniteType_cartan Tag.E6) p c Φ :=
    (levTwoS3a_data_congr levTwoS3a_root_eq_E6 LevTwoType.E6.rootFT
      (isFiniteType_cartan Tag.E6) p c Φ).1 hdata
  exact (levTwoS3a_tcRoot_congr levTwoS3a_root_eq_E6 LevTwoType.E6.rootFT
    (isFiniteType_cartan Tag.E6) Φ).2
    (levTwoS3a_engine_E6 h p hp hp2 c Φ hdata')

theorem levTwoEngine_F4_of_finite
    (h : ExcFinite Tag.F4 kacF4) : LevTwoEngine LevTwoType.F4 := by
  intro p hp hp2 c Φ hdata
  have hdata' : LevTwoData (isFiniteType_cartan Tag.F4) p c Φ :=
    (levTwoS3a_data_congr levTwoS3a_root_eq_F4 LevTwoType.F4.rootFT
      (isFiniteType_cartan Tag.F4) p c Φ).1 hdata
  exact (levTwoS3a_tcRoot_congr levTwoS3a_root_eq_F4 LevTwoType.F4.rootFT
    (isFiniteType_cartan Tag.F4) Φ).2
    (levTwoS3a_engine_F4 h p hp hp2 c Φ hdata')


end CFSG.StandardType.LevTwo
