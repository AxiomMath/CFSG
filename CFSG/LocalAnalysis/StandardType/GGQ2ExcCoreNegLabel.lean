module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import Certificates.Certificate13659
import CFSG.LocalAnalysis.StandardType.GGFamLabelKind
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormGe
import CFSG.LocalAnalysis.StandardType.GGLangRatNegOne
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4TwistOuter
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RKind
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
import CFSG.LieType.Chevalley.RootComponentType
import CFSG.LieType.Chevalley.CorootCoordinates
import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
import CFSG.HardMathSupport.Timmesfeld.RootAut.Count
import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighType
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section OrbitTables

open CFSG.HardMathSupport.Timmesfeld.RootAut TauCeti

@[expose] def cartanOrbitA8 : Fin 72 → Fin 8 → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0],
    ![0, 0, 1, 1, 1, 1, 0, 0],
    ![0, 0, 0, 1, 1, 1, 1, 0],
    ![0, 0, 0, 0, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 0, 0, 0],
    ![0, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 0, 0],
    ![0, 1, 1, 1, 1, 1, 1, 0],
    ![0, 0, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1],
    ![-1, 0, 0, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1],
    ![-1, -1, 0, 0, 0, 0, 0, 0],
    ![0, -1, -1, 0, 0, 0, 0, 0],
    ![0, 0, -1, -1, 0, 0, 0, 0],
    ![0, 0, 0, -1, -1, 0, 0, 0],
    ![0, 0, 0, 0, -1, -1, 0, 0],
    ![0, 0, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1],
    ![-1, -1, -1, 0, 0, 0, 0, 0],
    ![0, -1, -1, -1, 0, 0, 0, 0],
    ![0, 0, -1, -1, -1, 0, 0, 0],
    ![0, 0, 0, -1, -1, -1, 0, 0],
    ![0, 0, 0, 0, -1, -1, -1, 0],
    ![0, 0, 0, 0, 0, -1, -1, -1],
    ![-1, -1, -1, -1, 0, 0, 0, 0],
    ![0, -1, -1, -1, -1, 0, 0, 0],
    ![0, 0, -1, -1, -1, -1, 0, 0],
    ![0, 0, 0, -1, -1, -1, -1, 0],
    ![0, 0, 0, 0, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, 0, 0, 0],
    ![0, -1, -1, -1, -1, -1, 0, 0],
    ![0, 0, -1, -1, -1, -1, -1, 0],
    ![0, 0, 0, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, -1, 0, 0],
    ![0, -1, -1, -1, -1, -1, -1, 0],
    ![0, 0, -1, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, -1, -1, 0],
    ![0, -1, -1, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, -1, -1, -1]]

@[expose] def cartanOrbitReflA8 : Fin 72 → Fin 8 → Fin 72 :=
  ![![36, 8, 0, 0, 0, 0, 0, 0],
    ![8, 37, 9, 1, 1, 1, 1, 1],
    ![2, 9, 38, 10, 2, 2, 2, 2],
    ![3, 3, 10, 39, 11, 3, 3, 3],
    ![4, 4, 4, 11, 40, 12, 4, 4],
    ![5, 5, 5, 5, 12, 41, 13, 5],
    ![6, 6, 6, 6, 6, 13, 42, 14],
    ![7, 7, 7, 7, 7, 7, 14, 43],
    ![1, 0, 15, 8, 8, 8, 8, 8],
    ![15, 2, 1, 16, 9, 9, 9, 9],
    ![10, 16, 3, 2, 17, 10, 10, 10],
    ![11, 11, 17, 4, 3, 18, 11, 11],
    ![12, 12, 12, 18, 5, 4, 19, 12],
    ![13, 13, 13, 13, 19, 6, 5, 20],
    ![14, 14, 14, 14, 14, 20, 7, 6],
    ![9, 15, 8, 21, 15, 15, 15, 15],
    ![21, 10, 16, 9, 22, 16, 16, 16],
    ![17, 22, 11, 17, 10, 23, 17, 17],
    ![18, 18, 23, 12, 18, 11, 24, 18],
    ![19, 19, 19, 24, 13, 19, 12, 25],
    ![20, 20, 20, 20, 25, 14, 20, 13],
    ![16, 21, 21, 15, 26, 21, 21, 21],
    ![26, 17, 22, 22, 16, 27, 22, 22],
    ![23, 27, 18, 23, 23, 17, 28, 23],
    ![24, 24, 28, 19, 24, 24, 18, 29],
    ![25, 25, 25, 29, 20, 25, 25, 19],
    ![22, 26, 26, 26, 21, 30, 26, 26],
    ![30, 23, 27, 27, 27, 22, 31, 27],
    ![28, 31, 24, 28, 28, 28, 23, 32],
    ![29, 29, 32, 25, 29, 29, 29, 24],
    ![27, 30, 30, 30, 30, 26, 33, 30],
    ![33, 28, 31, 31, 31, 31, 27, 34],
    ![32, 34, 29, 32, 32, 32, 32, 28],
    ![31, 33, 33, 33, 33, 33, 30, 35],
    ![35, 32, 34, 34, 34, 34, 34, 31],
    ![34, 35, 35, 35, 35, 35, 35, 33],
    ![0, 44, 36, 36, 36, 36, 36, 36],
    ![44, 1, 45, 37, 37, 37, 37, 37],
    ![38, 45, 2, 46, 38, 38, 38, 38],
    ![39, 39, 46, 3, 47, 39, 39, 39],
    ![40, 40, 40, 47, 4, 48, 40, 40],
    ![41, 41, 41, 41, 48, 5, 49, 41],
    ![42, 42, 42, 42, 42, 49, 6, 50],
    ![43, 43, 43, 43, 43, 43, 50, 7],
    ![37, 36, 51, 44, 44, 44, 44, 44],
    ![51, 38, 37, 52, 45, 45, 45, 45],
    ![46, 52, 39, 38, 53, 46, 46, 46],
    ![47, 47, 53, 40, 39, 54, 47, 47],
    ![48, 48, 48, 54, 41, 40, 55, 48],
    ![49, 49, 49, 49, 55, 42, 41, 56],
    ![50, 50, 50, 50, 50, 56, 43, 42],
    ![45, 51, 44, 57, 51, 51, 51, 51],
    ![57, 46, 52, 45, 58, 52, 52, 52],
    ![53, 58, 47, 53, 46, 59, 53, 53],
    ![54, 54, 59, 48, 54, 47, 60, 54],
    ![55, 55, 55, 60, 49, 55, 48, 61],
    ![56, 56, 56, 56, 61, 50, 56, 49],
    ![52, 57, 57, 51, 62, 57, 57, 57],
    ![62, 53, 58, 58, 52, 63, 58, 58],
    ![59, 63, 54, 59, 59, 53, 64, 59],
    ![60, 60, 64, 55, 60, 60, 54, 65],
    ![61, 61, 61, 65, 56, 61, 61, 55],
    ![58, 62, 62, 62, 57, 66, 62, 62],
    ![66, 59, 63, 63, 63, 58, 67, 63],
    ![64, 67, 60, 64, 64, 64, 59, 68],
    ![65, 65, 68, 61, 65, 65, 65, 60],
    ![63, 66, 66, 66, 66, 62, 69, 66],
    ![69, 64, 67, 67, 67, 67, 63, 70],
    ![68, 70, 65, 68, 68, 68, 68, 64],
    ![67, 69, 69, 69, 69, 69, 66, 71],
    ![71, 68, 70, 70, 70, 70, 70, 67],
    ![70, 71, 71, 71, 71, 71, 71, 69]]

@[expose] def cartanOrbitE6 : Fin 72 → Fin 6 → ℤ :=
  ![![1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 1, 0, 0],
    ![0, 1, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 0],
    ![0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 1, 1],
    ![1, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 0],
    ![0, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0],
    ![1, 1, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 1],
    ![1, 1, 2, 2, 1, 0],
    ![1, 1, 1, 2, 1, 1],
    ![0, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 1, 1],
    ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1],
    ![1, 2, 2, 3, 2, 1],
    ![-1, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, -1],
    ![-1, 0, -1, 0, 0, 0],
    ![0, -1, 0, -1, 0, 0],
    ![0, 0, -1, -1, 0, 0],
    ![0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, -1, -1],
    ![-1, 0, -1, -1, 0, 0],
    ![0, -1, -1, -1, 0, 0],
    ![0, -1, 0, -1, -1, 0],
    ![0, 0, -1, -1, -1, 0],
    ![0, 0, 0, -1, -1, -1],
    ![-1, -1, -1, -1, 0, 0],
    ![-1, 0, -1, -1, -1, 0],
    ![0, -1, -1, -1, -1, 0],
    ![0, -1, 0, -1, -1, -1],
    ![0, 0, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, 0],
    ![-1, 0, -1, -1, -1, -1],
    ![0, -1, -1, -2, -1, 0],
    ![0, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -2, -1, 0],
    ![-1, -1, -1, -1, -1, -1],
    ![0, -1, -1, -2, -1, -1],
    ![-1, -1, -2, -2, -1, 0],
    ![-1, -1, -1, -2, -1, -1],
    ![0, -1, -1, -2, -2, -1],
    ![-1, -1, -2, -2, -1, -1],
    ![-1, -1, -1, -2, -2, -1],
    ![-1, -1, -2, -2, -2, -1],
    ![-1, -1, -2, -3, -2, -1],
    ![-1, -2, -2, -3, -2, -1]]

@[expose] def cartanOrbitReflE6 : Fin 72 → Fin 6 → Fin 72 :=
  ![![36, 0, 6, 0, 0, 0],
    ![1, 37, 1, 7, 1, 1],
    ![6, 2, 38, 8, 2, 2],
    ![3, 7, 8, 39, 9, 3],
    ![4, 4, 4, 9, 40, 10],
    ![5, 5, 5, 5, 10, 41],
    ![2, 6, 0, 11, 6, 6],
    ![7, 3, 12, 1, 13, 7],
    ![11, 12, 3, 2, 14, 8],
    ![9, 13, 14, 4, 3, 15],
    ![10, 10, 10, 15, 5, 4],
    ![8, 16, 11, 6, 17, 11],
    ![16, 8, 7, 12, 18, 12],
    ![13, 9, 18, 13, 7, 19],
    ![17, 18, 9, 14, 8, 20],
    ![15, 19, 20, 10, 15, 9],
    ![12, 11, 16, 16, 21, 16],
    ![14, 21, 17, 17, 11, 22],
    ![21, 14, 13, 23, 12, 24],
    ![19, 15, 24, 19, 19, 13],
    ![22, 24, 15, 20, 20, 14],
    ![18, 17, 21, 25, 16, 26],
    ![20, 26, 22, 22, 22, 17],
    ![25, 23, 23, 18, 23, 27],
    ![26, 20, 19, 27, 24, 18],
    ![23, 25, 28, 21, 25, 29],
    ![24, 22, 26, 29, 26, 21],
    ![29, 27, 27, 24, 30, 23],
    ![28, 28, 25, 28, 28, 31],
    ![27, 29, 31, 26, 32, 25],
    ![32, 30, 30, 30, 27, 30],
    ![31, 31, 29, 31, 33, 28],
    ![30, 32, 33, 32, 29, 32],
    ![33, 33, 32, 34, 31, 33],
    ![34, 35, 34, 33, 34, 34],
    ![35, 34, 35, 35, 35, 35],
    ![0, 36, 42, 36, 36, 36],
    ![37, 1, 37, 43, 37, 37],
    ![42, 38, 2, 44, 38, 38],
    ![39, 43, 44, 3, 45, 39],
    ![40, 40, 40, 45, 4, 46],
    ![41, 41, 41, 41, 46, 5],
    ![38, 42, 36, 47, 42, 42],
    ![43, 39, 48, 37, 49, 43],
    ![47, 48, 39, 38, 50, 44],
    ![45, 49, 50, 40, 39, 51],
    ![46, 46, 46, 51, 41, 40],
    ![44, 52, 47, 42, 53, 47],
    ![52, 44, 43, 48, 54, 48],
    ![49, 45, 54, 49, 43, 55],
    ![53, 54, 45, 50, 44, 56],
    ![51, 55, 56, 46, 51, 45],
    ![48, 47, 52, 52, 57, 52],
    ![50, 57, 53, 53, 47, 58],
    ![57, 50, 49, 59, 48, 60],
    ![55, 51, 60, 55, 55, 49],
    ![58, 60, 51, 56, 56, 50],
    ![54, 53, 57, 61, 52, 62],
    ![56, 62, 58, 58, 58, 53],
    ![61, 59, 59, 54, 59, 63],
    ![62, 56, 55, 63, 60, 54],
    ![59, 61, 64, 57, 61, 65],
    ![60, 58, 62, 65, 62, 57],
    ![65, 63, 63, 60, 66, 59],
    ![64, 64, 61, 64, 64, 67],
    ![63, 65, 67, 62, 68, 61],
    ![68, 66, 66, 66, 63, 66],
    ![67, 67, 65, 67, 69, 64],
    ![66, 68, 69, 68, 65, 68],
    ![69, 69, 68, 70, 67, 69],
    ![70, 71, 70, 69, 70, 70],
    ![71, 70, 71, 71, 71, 71]]

theorem cartanOrbitA8_single : ∀ i : Fin 8,
    cartanOrbitA8 (Fin.castLE (by norm_num) i) = Pi.single i 1 := by
  decide +kernel

theorem cartanOrbitA8_refl : ∀ (k : Fin 72) (i : Fin 8) (j : Fin 8),
    coordReflect (CartanMatrix.A 8) i (cartanOrbitA8 k) j =
      cartanOrbitA8 (cartanOrbitReflA8 k i) j := by
  decide +kernel

theorem cartanOrbitA8_injective : ∀ k l : Fin 72,
    cartanOrbitA8 k = cartanOrbitA8 l → k = l := by
  decide +kernel

theorem cartanOrbitA8_orthCount :
    ((Finset.univ : Finset (Fin 72 × Fin 72)).filter fun p =>
      ∑ i, ∑ j, cartanOrbitA8 p.1 i * CartanMatrix.A 8 i j * cartanOrbitA8 p.2 j = 0).card =
      3024 := by
  decide +kernel

theorem cartanOrbitE6_single : ∀ i : Fin 6,
    cartanOrbitE6 (Fin.castLE (by norm_num) i) = Pi.single i 1 := by
  decide +kernel

theorem cartanOrbitE6_refl : ∀ (k : Fin 72) (i : Fin 6) (j : Fin 6),
    coordReflect (CartanMatrix.E 6) i (cartanOrbitE6 k) j =
      cartanOrbitE6 (cartanOrbitReflE6 k i) j := by
  decide +kernel

theorem cartanOrbitE6_injective : ∀ k l : Fin 72,
    cartanOrbitE6 k = cartanOrbitE6 l → k = l := by
  decide +kernel

theorem cartanOrbitE6_orthCount :
    ((Finset.univ : Finset (Fin 72 × Fin 72)).filter fun p =>
      ∑ i, ∑ j, cartanOrbitE6 p.1 i * CartanMatrix.E 6 i j * cartanOrbitE6 p.2 j = 0).card =
      2160 := by
  decide +kernel

theorem _root_.CFSG.HardMathSupport.Timmesfeld.RootAut.IsOrbitRoot.mem_range {n N : ℕ}
    {M : Matrix (Fin n) (Fin n) ℤ} {R : Fin N → Fin n → ℤ}
    (hsingle : ∀ i : Fin n, ∃ k : Fin N, R k = Pi.single i 1)
    (hrefl : ∀ (k : Fin N) (i : Fin n), ∃ l : Fin N, R l = coordReflect M i (R k))
    {x : Fin n → ℤ} (hx : IsOrbitRoot M x) : x ∈ Set.range R := by
  induction hx with
  | single i => exact hsingle i
  | reflect i _ ih =>
      obtain ⟨k, rfl⟩ := ih
      exact hrefl k i

theorem ncard_orthPairs_eq_filter {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {n N : ℕ} (e : simpleRoots Ψ ≃ Fin n) {M : Matrix (Fin n) (Fin n) ℤ}
    (hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2)
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ))
    (R : Fin N → Fin n → ℤ) (hR : Function.Injective R)
    (horbit : {x | IsOrbitRoot M x} = Set.range R) :
    {p : (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) |
        p.1 ∈ Ψ ∧ p.2 ∈ Ψ ∧ iform p.1 p.2 = 0}.ncard =
      ((Finset.univ : Finset (Fin N × Fin N)).filter fun p =>
        ∑ i, ∑ j, R p.1 i * M i j * R p.2 j = 0).card := by
  classical
  let G : Fin N × Fin N → (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) :=
    fun p => (rootLift e (R p.1), rootLift e (R p.2))
  let T : Finset (Fin N × Fin N) :=
    Finset.univ.filter fun p => ∑ i, ∑ j, R p.1 i * M i j * R p.2 j = 0
  have hG : Function.Injective G := by
    rintro ⟨k, l⟩ ⟨k', l'⟩ h
    simp only [G, Prod.mk.injEq] at h
    have h1 := rootLift_injective hΨ e h.1
    have h2 := rootLift_injective hΨ e h.2
    have hk := hR h1
    have hl := hR h2
    simp [hk, hl]
  have hset : {p : (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) |
        p.1 ∈ Ψ ∧ p.2 ∈ Ψ ∧ iform p.1 p.2 = 0} = G '' (T : Set _) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨h1, h2, h0⟩
      rw [← image_rootLift_orbit hΨ e he] at h1 h2
      obtain ⟨x, hx, hqx⟩ := h1
      obtain ⟨y, hy, hqy⟩ := h2
      rw [horbit] at hx hy
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨l, rfl⟩ := hy
      refine ⟨(k, l), ?_, Prod.ext hqx hqy⟩
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← iform_rootLift hsl e he]
      simpa only [hqx, hqy] using h0
    · rintro ⟨⟨k, l⟩, hT, hq⟩
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      have h1 := congrArg Prod.fst hq
      have h2 := congrArg Prod.snd hq
      refine ⟨?_, ?_, ?_⟩
      · rw [← h1, ← image_rootLift_orbit hΨ e he]
        exact ⟨R k, by rw [horbit]; exact Set.mem_range_self k, rfl⟩
      · rw [← h2, ← image_rootLift_orbit hΨ e he]
        exact ⟨R l, by rw [horbit]; exact Set.mem_range_self l, rfl⟩
      · rw [← h1, ← h2, iform_rootLift hsl e he]
        exact hT
  rw [hset, Set.ncard_image_of_injective _ hG, Set.ncard_coe_finset]

theorem dynkinType_eq_A8_or_E6_of_numRoots_eq_seventyTwo {t : DynkinType}
    (ht : t.Valid) (hts : t.IsSimplyLaced) (hr : t.rank ≤ 8) (h72 : t.numRoots = 72) :
    t = .A 8 ∨ t = .E6 := by
  cases t with
  | A n =>
      simp only [DynkinType.numRoots_A, DynkinType.rank_A] at h72 hr
      have hn : 1 ≤ n := (DynkinType.valid_A).1 ht
      interval_cases n <;> simp_all
  | B n => exact absurd hts (DynkinType.not_isSimplyLaced_B n)
  | C n => exact absurd hts (DynkinType.not_isSimplyLaced_C n)
  | D n =>
      simp only [DynkinType.numRoots_D, DynkinType.rank_D] at h72 hr
      have hn : 4 ≤ n := (DynkinType.valid_D).1 ht
      interval_cases n <;> norm_num at h72
  | E6 => exact Or.inr rfl
  | E7 => rw [DynkinType.numRoots_E7] at h72; omega
  | E8 => rw [DynkinType.numRoots_E8] at h72; omega
  | F4 => exact absurd hts DynkinType.not_isSimplyLaced_F4
  | G2 => exact absurd hts DynkinType.not_isSimplyLaced_G2

theorem cartanOrbitA8_orbit_eq_range {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (e : simpleRoots Ψ ≃ Fin 8)
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      (CartanMatrix.A 8) (e β) (e γ)) (h72 : Ψ.ncard = 72) :
    {x | IsOrbitRoot (CartanMatrix.A 8) x} = Set.range cartanOrbitA8 := by
  refine Set.eq_of_subset_of_ncard_le (fun x hx => IsOrbitRoot.mem_range
    (fun i => ⟨_, cartanOrbitA8_single i⟩)
    (fun k i => ⟨_, funext fun j => (cartanOrbitA8_refl k i j).symm⟩) hx) ?_
  rw [Set.ncard_range_of_injective cartanOrbitA8_injective, ← ncard_eq_ncard_orbit hΨ e he, h72]
  simp

theorem cartanOrbitE6_orbit_eq_range {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (e : simpleRoots Ψ ≃ Fin 6)
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      (CartanMatrix.E 6) (e β) (e γ)) (h72 : Ψ.ncard = 72) :
    {x | IsOrbitRoot (CartanMatrix.E 6) x} = Set.range cartanOrbitE6 := by
  refine Set.eq_of_subset_of_ncard_le (fun x hx => IsOrbitRoot.mem_range
    (fun i => ⟨_, cartanOrbitE6_single i⟩)
    (fun k i => ⟨_, funext fun j => (cartanOrbitE6_refl k i j).symm⟩) hx) ?_
  rw [Set.ncard_range_of_injective cartanOrbitE6_injective, ← ncard_eq_ncard_orbit hΨ e he, h72]
  simp

end OrbitTables


open CFSG.HardMathSupport.Timmesfeld.RootAut in
theorem not_twistInner_neg_of_coord {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {n : ℕ} (e : simpleRoots Ψ ≃ Fin n)
    {M : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ))
    (c : Fin n → ℤ) (d : ℤ) (hd : ∀ j, d ∣ ∑ i, c i * M i j)
    (hnd : ¬ d * d ∣ 2 * ∑ i, ∑ j, c i * M i j * c j) :
    ¬ twistInner Ψ (fun γ => -γ) := by
  classical
  have hslΨ : ∀ γ ∈ Ψ, iform γ γ = 2 :=
    fun γ hγ => by
      rw [← dotProduct_mulVec_eq_iform]
      exact rootForm_self hτ (hΨ.isRoot γ hγ)
  have hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2 :=
    fun β hβ => hslΨ β (simpleRoots_subset hβ)
  have hμ : rootLift e c ∈ Submodule.span ℤ Ψ := by
    rw [rootLift_eq_sum]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (simpleRoots_subset (e.symm j).2)
  have hμd : ∀ γ ∈ Ψ, d ∣ iform (rootLift e c) γ := by
    intro γ hγ
    rw [← image_rootLift_orbit hΨ e he] at hγ
    obtain ⟨x, -, rfl⟩ := hγ
    rw [iform_rootLift hsl e he, Finset.sum_comm]
    refine Finset.dvd_sum fun j _ => ?_
    rw [← Finset.sum_mul]
    simpa [mul_comm] using dvd_mul_of_dvd_right (hd j) (x j)
  have hnd' : ¬ d * d ∣ iform (rootLift e c)
      ((-AddMonoidHom.id (Fin τ.rank → ℤ)) (rootLift e c) - rootLift e c) := by
    have h2 : (-AddMonoidHom.id (Fin τ.rank → ℤ)) (rootLift e c) - rootLift e c =
        (-2 : ℤ) • rootLift e c := by
      rw [AddMonoidHom.neg_apply, AddMonoidHom.id_apply]
      module
    rw [h2, iform_smul_right, iform_rootLift hsl e he c c]
    rw [show (-2 : ℤ) * (∑ i, ∑ j, c i * M i j * c j) =
      -(2 * ∑ i, ∑ j, c i * M i j * c j) by ring, dvd_neg]
    exact hnd
  have hnot := not_twistInner_of_disc hΨ.isRoot hslΨ
    (-AddMonoidHom.id (Fin τ.rank → ℤ)) hμ hμd hμd hnd'
  intro h
  refine hnot ((twistInner_congr (σ := ((fun x => -x) : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)))
    (σ' := fun γ => -γ) ?_).mpr h)
  intro γ _
  rfl


open TauCeti CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.StandardType.LangRat in
theorem twistInner_neg_iff {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty) :
    twistInner Ψ (fun γ => -γ) ↔
      compRank Ψ = 1 ∨ (4 ≤ compRank Ψ ∧ Even (compRank Ψ) ∧
          Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) ∨
        (compRank Ψ = 7 ∧ Ψ.ncard = 126) ∨ (compRank Ψ = 8 ∧ Ψ.ncard = 240) := by
  classical
  obtain ⟨t, e, ht, hsl, hiform, hcard, hN⟩ := exists_dynkinType hτ hΨ hne
  have he' : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ) :=
    fun β γ => (corootPair_eq_iform_of_simplyLaced hτ (simpleRoots_isRoot β.2) γ).trans
      (hiform β γ)
  have hr : compRank Ψ = t.rank := (compRank_eq_card hΨ).trans hcard
  have h8 : t.rank ≤ 8 := hr ▸ (compRank_le Ψ).trans (by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide)
  rw [hr, hN]
  rcases mem_rigidTypes_or_mem_countTypes ht h8 with hmem | hmem
  · simp only [rigidTypes, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hsl (by decide)
    | exact ⟨fun _ => by decide, fun _ => langRatNegOne_twistInner_of_type hΨ e he'
        (Or.inl (by simp [rigidTypes]))⟩
  · simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.A 2).cartanMatrix)
        (c := fun i => (2 : ℤ) - i) 3 ?_ ?_
      · rw [DynkinType.cartanMatrix_A]; decide
      · rw [DynkinType.cartanMatrix_A]; decide
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.A 3).cartanMatrix)
        (c := fun i => (3 : ℤ) - i) 4 ?_ ?_
      · rw [DynkinType.cartanMatrix_A]; decide
      · rw [DynkinType.cartanMatrix_A]; decide
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.A 4).cartanMatrix)
        (c := fun i => (4 : ℤ) - i) 5 ?_ ?_
      · rw [DynkinType.cartanMatrix_A]; decide
      · rw [DynkinType.cartanMatrix_A]; decide
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.A 5).cartanMatrix)
        (c := fun i => (5 : ℤ) - i) 6 ?_ ?_
      · rw [DynkinType.cartanMatrix_A]; decide
      · rw [DynkinType.cartanMatrix_A]; decide
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.A 6).cartanMatrix)
        (c := fun i => (6 : ℤ) - i) 7 ?_ ?_
      · rw [DynkinType.cartanMatrix_A]; decide
      · rw [DynkinType.cartanMatrix_A]; decide
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.A 7).cartanMatrix)
        (c := fun i => (7 : ℤ) - i) 8 ?_ ?_
      · rw [DynkinType.cartanMatrix_A]; decide
      · rw [DynkinType.cartanMatrix_A]; decide
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.A 8).cartanMatrix)
        (c := fun i => (8 : ℤ) - i) 9 ?_ ?_
      · rw [DynkinType.cartanMatrix_A]; decide
      · rw [DynkinType.cartanMatrix_A]; decide
    ·
      exact ⟨fun _ => by decide, fun _ => langRatNegOne_twistInner_of_type (t := .D 4) hΨ e he'
        (Or.inr (Or.inl rfl))⟩
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.D 5).cartanMatrix)
        (c := ![2, 4, 6, 3, 5]) 4 ?_ ?_
      · rw [DynkinType.cartanMatrix_D]; decide
      · rw [DynkinType.cartanMatrix_D]; decide
    ·
      exact ⟨fun _ => by decide, fun _ => langRatNegOne_twistInner_of_type (t := .D 6) hΨ e he'
        (Or.inr (Or.inr (Or.inl rfl)))⟩
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.D 7).cartanMatrix)
        (c := ![2, 4, 6, 8, 10, 5, 7]) 4 ?_ ?_
      · rw [DynkinType.cartanMatrix_D]; decide
      · rw [DynkinType.cartanMatrix_D]; decide
    ·
      exact ⟨fun _ => by decide, fun _ => langRatNegOne_twistInner_of_type (t := .D 8) hΨ e he'
        (Or.inr (Or.inr (Or.inr rfl)))⟩
    ·
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
      refine not_twistInner_neg_of_coord hτ hΨ e he' (M := (DynkinType.E6).cartanMatrix)
        (c := ![4, 3, 5, 6, 4, 2]) 3 ?_ ?_
      · rw [DynkinType.cartanMatrix_E6, CartanMatrix.E_six_eq]; decide
      · rw [DynkinType.cartanMatrix_E6, CartanMatrix.E_six_eq]; decide

open Classical in
theorem twistKindOf_of_neg {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hne : Ψ.Nonempty) (hρ : ∀ γ ∈ Ψ, ρ γ = -γ) :
    twistKindOf ρ Ψ =
      if twistInner Ψ (fun γ => -γ) then TwistKind.inner
      else if compRank Ψ = 6 ∧ Ψ.ncard = 72 then TwistKind.exc
      else if 4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1) then TwistKind.twoD
      else TwistKind.suN := by
  have hfin : Ψ.Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hρmem : ∀ γ ∈ Ψ, ρ γ ∈ Ψ := fun γ hγ => by
    rw [hρ γ hγ]
    exact hΨ.neg_mem γ hγ
  have hlen : componentOrbitLength ρ Ψ = 1 := componentOrbitLength_eq_one hfin hρmem
  have h1 : ∀ γ ∈ Ψ,
      (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ] γ = -γ := by
    intro γ hγ
    rw [hlen, Function.iterate_one]
    exact hρ γ hγ
  have h2 : ∀ γ ∈ Ψ,
      (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ] γ = γ := by
    intro γ hγ
    rw [hlen]
    norm_num
    rw [hρ (ρ γ) (hρmem γ hγ), hρ γ hγ, neg_neg]
  have hinner : twistInner Ψ
      ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]) ↔
      twistInner Ψ (fun γ => -γ) := twistInner_congr h1
  have htwo : twistInner Ψ
      ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ]) := by
    refine (twistInner_congr h2).2 ?_
    exact ⟨1, Subgroup.one_mem _, fun γ _ => by simp⟩
  by_cases hneg : twistInner Ψ (fun γ => -γ)
  · unfold twistKindOf
    rw [if_pos (hinner.2 hneg), if_pos hneg]
  · have hnot : ¬ twistInner Ψ
        ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]) :=
      fun h => hneg (hinner.1 h)
    unfold twistKindOf
    rw [if_neg hnot, if_neg hneg]
    by_cases hE : compRank Ψ = 6 ∧ Ψ.ncard = 72
    · rw [if_pos (Or.inl hE), if_pos hE]
    · have hnotExc : ¬ ((compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨
          (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
            ¬ twistInner Ψ
              ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ]))) := by
        rintro (h | ⟨-, -, h⟩)
        · exact hE h
        · exact h htwo
      rw [if_neg hnotExc, if_neg hE]
      by_cases hD : 4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)
      · rw [if_pos hD, if_pos hD]
      · rw [if_neg hD, if_neg hD]
        have hAshape : 2 ≤ compRank Ψ ∧ Ψ.ncard = compRank Ψ * (compRank Ψ + 1) := by
          rcases CFSG.StandardType.LieKnownR2.ExcPos.compRank_ncard_ade hτ hΨ hne with
            hk1 | hkA | hkD | hkE6 | hkE7 | hkE8
          · exact absurd ((twistInner_neg_iff hτ hΨ hne).2 (Or.inl hk1)) hneg
          · exact hkA
          · exact absurd hkD hD
          · exact absurd hkE6 hE
          · exact absurd ((twistInner_neg_iff hτ hΨ hne).2
              (Or.inr (Or.inr (Or.inl hkE7)))) hneg
          · exact absurd ((twistInner_neg_iff hτ hΨ hne).2
              (Or.inr (Or.inr (Or.inr hkE8)))) hneg
        rw [if_pos hAshape]

theorem ncard_orthPairs_of_ncard_eq_seventyTwo {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (h72 : Ψ.ncard = 72) :
    {p : (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) | p.1 ∈ Ψ ∧ p.2 ∈ Ψ ∧ iform p.1 p.2 = 0}.ncard =
      if compRank Ψ = 8 then 3024 else 2160 := by
  classical
  have hne : Ψ.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨t, e, ht, hts, hform, hcard, hnum⟩ := exists_dynkinType hτ hΨ hne
  have hnum72 : t.numRoots = 72 := by omega
  have hcomp : compRank Ψ = t.rank := by
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ, hcard]
  have hr8 : t.rank ≤ 8 := hcomp ▸
    (CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le Ψ).trans
      (CFSG.HardMathSupport.Timmesfeld.RootAut.rank_le_eight τ)
  have hcases := dynkinType_eq_A8_or_E6_of_numRoots_eq_seventyTwo ht hts hr8 hnum72
  have hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (simpleRoots_isRoot hβ)
  have he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ =>
    (corootPair_eq_iform_of_simplyLaced hτ (simpleRoots_isRoot β.2) γ).trans (hform β γ)
  rcases hcases with htA | htE
  · subst htA
    have heA : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
        (CartanMatrix.A 8) (e β) (e γ) := by
      simpa only [TauCeti.DynkinType.cartanMatrix_A] using he
    have hcomp8 : compRank Ψ = 8 := by simpa [TauCeti.DynkinType.rank_A] using hcomp
    have horbit := cartanOrbitA8_orbit_eq_range hΨ e heA h72
    have hcount := ncard_orthPairs_eq_filter hΨ e hsl heA cartanOrbitA8
      cartanOrbitA8_injective horbit
    rw [hcount, if_pos hcomp8]
    exact cartanOrbitA8_orthCount
  · subst htE
    have heE : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
        (CartanMatrix.E 6) (e β) (e γ) := by
      simpa only [TauCeti.DynkinType.cartanMatrix_E6] using he
    have hcomp6 : compRank Ψ = 6 := by simpa [TauCeti.DynkinType.rank_E6] using hcomp
    have horbit := cartanOrbitE6_orbit_eq_range hΨ e heE h72
    have hcount := ncard_orthPairs_eq_filter hΨ e hsl heE cartanOrbitE6
      cartanOrbitE6_injective horbit
    rw [hcount, if_neg (by omega : compRank Ψ ≠ 8)]
    exact cartanOrbitE6_orthCount

end CFSG.StandardType.TableCRes

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes

noncomputable section


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}

def codeRootSign (d : ExcCoordDatum S T₀ m) (q : ExcRaw.Root m × Bool) :
    Fin τ.rank → ℤ :=
  match q.2 with
  | true => d.γ q.1
  | false => -d.γ q.1

theorem codeRootSign_injective (d : ExcCoordDatum S T₀ m) :
    Function.Injective (codeRootSign d) := by
  rintro ⟨i, b⟩ ⟨j, b'⟩ h
  have hns : d.γ i ≠ -d.γ i := by
    intro h0
    exact (d.isRoot i).ne_zero (by
      funext k
      have hk := congrFun h0 k
      simp only [Pi.neg_apply, Pi.zero_apply] at hk ⊢
      omega)
  have h' : d.γ i = d.γ j ∨ d.γ i = -d.γ j := by
    rcases b with _ | _ <;> rcases b' with _ | _ <;> simp only [codeRootSign] at h ⊢
    · exact Or.inl (neg_inj.mp h)
    · exact Or.inr (by rw [← h, neg_neg])
    · exact Or.inr h
    · exact Or.inl h
  have hij : i = j := d.eq_of_eq i j h'
  subst hij
  rcases b with _ | _ <;> rcases b' with _ | _ <;> simp only [codeRootSign] at h ⊢
  · exfalso
    exact hns h.symm
  · exfalso
    exact hns h

theorem codeRoots_eq_image (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)) :
    codeRoots d.γ c =
      codeRootSign d '' ((c ×ˢ (Finset.univ : Finset Bool)) : Set (ExcRaw.Root m × Bool)) := by
  ext δ
  simp only [codeRoots, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨i, hi, h | h⟩
    · exact ⟨(i, true), ⟨hi, Finset.mem_univ _⟩, by simp [codeRootSign, h]⟩
    · exact ⟨(i, false), ⟨hi, Finset.mem_univ _⟩, by simp [codeRootSign, h]⟩
  · rintro ⟨⟨i, b⟩, ⟨hi, -⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    cases b
    · exact Or.inr (by simp [codeRootSign])
    · exact Or.inl (by simp [codeRootSign])

theorem iform_codeRootSign_eq_zero_iff (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (d : ExcCoordDatum S T₀ m) (i j : ExcRaw.Root m) (b b' : Bool) :
    iform (codeRootSign d (i, b)) (codeRootSign d (j, b')) = 0 ↔
      ExcRaw.pairing m i j = 0 := by
  have hp : ExcRaw.pairing m i j = iform (d.γ i) (d.γ j) := by
    rw [d.pairing_eq i j,
      corootPair_eq_iform_of_simplyLaced hτ (d.isRoot j) (d.γ i),
      iform_comm]
  rw [hp]
  rcases b with _ | _ <;> rcases b' with _ | _ <;>
    simp [codeRootSign, CFSG.LieType.Chevalley.SimplyLacedCover.iform_neg_left,
      CFSG.LieType.Chevalley.SimplyLacedCover.iform_neg_right]

theorem ncard_orthPairs_codeRoots (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)) :
    {q : (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) |
        q.1 ∈ codeRoots d.γ c ∧ q.2 ∈ codeRoots d.γ c ∧ iform q.1 q.2 = 0}.ncard =
      4 * ExcRaw.orthCount m c := by
  classical
  let V : Finset ((ExcRaw.Root m × ExcRaw.Root m) × (Bool × Bool)) :=
    ((c ×ˢ c).filter fun q => ExcRaw.pairing m q.1 q.2 = 0) ×ˢ
      (Finset.univ : Finset (Bool × Bool))
  let g : ((ExcRaw.Root m × ExcRaw.Root m) × (Bool × Bool)) →
      (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) :=
    fun q => (codeRootSign d (q.1.1, q.2.1), codeRootSign d (q.1.2, q.2.2))
  have hQ : {q : (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) |
        q.1 ∈ codeRoots d.γ c ∧ q.2 ∈ codeRoots d.γ c ∧ iform q.1 q.2 = 0} =
      g '' (V : Set _) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨h1, h2, h0⟩
      rw [codeRoots_eq_image d c] at h1 h2
      obtain ⟨⟨i, b⟩, ⟨hi, -⟩, hqi⟩ := h1
      obtain ⟨⟨j, b'⟩, ⟨hj, -⟩, hqj⟩ := h2
      refine ⟨((i, j), (b, b')), ?_, Prod.ext hqi hqj⟩
      simp only [V, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, and_true]
      refine ⟨⟨hi, hj⟩, ?_⟩
      rw [← hqi, ← hqj] at h0
      exact (iform_codeRootSign_eq_zero_iff hτ d i j b b').1 h0
    · rintro ⟨⟨⟨i, j⟩, ⟨b, b'⟩⟩, hmem, hq⟩
      simp only [V, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, and_true] at hmem
      obtain ⟨⟨hi, hj⟩, hp⟩ := hmem
      have h1 := congrArg Prod.fst hq
      have h2 := congrArg Prod.snd hq
      refine ⟨?_, ?_, ?_⟩
      · rw [← h1, codeRoots_eq_image d c]
        exact ⟨(i, b), ⟨hi, Finset.mem_univ _⟩, rfl⟩
      · rw [← h2, codeRoots_eq_image d c]
        exact ⟨(j, b'), ⟨hj, Finset.mem_univ _⟩, rfl⟩
      · rw [← h1, ← h2, iform_codeRootSign_eq_zero_iff hτ d i j b b']
        exact hp
  have hg : Function.Injective g := by
    rintro ⟨⟨i, j⟩, ⟨b, b'⟩⟩ ⟨⟨i', j'⟩, ⟨b'', b'''⟩⟩ h
    simp only [g, Prod.mk.injEq] at h
    have h1 := codeRootSign_injective d h.1
    have h2 := codeRootSign_injective d h.2
    simp only [Prod.mk.injEq] at h1 h2 ⊢
    exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
  rw [hQ, Set.ncard_image_of_injective _ hg, Set.ncard_coe_finset]
  simp only [V, Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    ExcRaw.orthCount]
  ring


theorem componentLabel_codeRoots_eq_labelSL (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (d : ExcCoordDatum S T₀ m) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    {c : Finset (ExcRaw.Root m)} (hΨ : IsRootComponent (codeRoots d.γ c)) (hc : c.Nonempty) :
    componentLabel (compRank (codeRoots d.γ c)) (codeRoots d.γ c).ncard
        (twistKindOf S.ρ (codeRoots d.γ c)) 1 = ExcRaw.labelSL c.card (ExcRaw.orthCount m c) := by
  classical
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨i₀, hi₀⟩ := hc
  have hne : (codeRoots d.γ c).Nonempty := ⟨d.γ i₀, i₀, hi₀, Or.inl rfl⟩
  have hρΨ : ∀ γ ∈ codeRoots d.γ c, S.ρ γ = -γ := by
    rintro γ ⟨j, hj, rfl | rfl⟩
    · exact hρ _ (d.isRoot j)
    · exact hρ _ (IsRoot.neg (d.isRoot j))
  have hkind := twistKindOf_of_neg hτ' hΨ hne hρΨ
  have hN : (codeRoots d.γ c).ncard = 2 * c.card := d.ncard_codeRoots c
  have hle : compRank (codeRoots d.γ c) ≤ 8 :=
    (CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le _).trans
      (CFSG.HardMathSupport.Timmesfeld.RootAut.rank_le_eight τ)
  have hOP := ncard_orthPairs_codeRoots hτ' d c
  generalize hΨdef : codeRoots d.γ c = Ψ at *
  rcases CFSG.StandardType.LieKnownR2.ExcPos.compRank_ncard_ade hτ' hΨ hne with
    h1 | ⟨h2, hA⟩ | ⟨h4, hD⟩ | ⟨h6, h72⟩ | ⟨h7, h126⟩ | ⟨h8, h240⟩
  ·
    have h2' : Ψ.ncard = 2 := by
      obtain ⟨t, ht, hsl, hrank, hNt⟩ :=
        CFSG.StandardType.LieKnownR2.ExcPos.exists_dynkinType_compRank hτ' hΨ (by omega)
      rw [h1] at hrank
      cases t with
      | A n =>
        rw [TauCeti.DynkinType.rank_A] at hrank
        rw [TauCeti.DynkinType.numRoots_A, ← hrank] at hNt
        rw [hNt]
      | B n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_B n)
      | C n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_C n)
      | D n =>
        rw [TauCeti.DynkinType.rank_D] at hrank
        have h4 := TauCeti.DynkinType.valid_D.1 ht
        omega
      | E6 =>
        rw [TauCeti.DynkinType.rank_E6] at hrank
        omega
      | E7 =>
        rw [TauCeti.DynkinType.rank_E7] at hrank
        omega
      | E8 =>
        rw [TauCeti.DynkinType.rank_E8] at hrank
        omega
      | F4 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_F4
      | G2 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_G2
    have hc1 : c.card = 1 := by omega
    have hneg : twistInner Ψ (fun γ => -γ) :=
      (twistInner_neg_iff hτ' hΨ hne).2 (Or.inl h1)
    rw [hkind, if_pos hneg, h1, h2', hc1]
    norm_num [componentLabel, ExcRaw.labelSL]
  ·
    have hcA : c.card = Ψ.ncard / 2 :=
      Nat.eq_div_of_mul_eq_right (by norm_num) hN.symm
    by_cases h8 : compRank Ψ = 8
    ·
      have h72' : Ψ.ncard = 72 := by rw [hA, h8]
      have hc36 : c.card = 36 := by omega
      have hni : ¬ twistInner Ψ (fun γ => -γ) := by
        rw [twistInner_neg_iff hτ' hΨ hne, h8, h72']
        norm_num
      have ho : ExcRaw.orthCount m c = 756 := by
        have h2'' := ncard_orthPairs_of_ncard_eq_seventyTwo hτ' hΨ h72'
        rw [h8] at h2''
        simp at h2''
        have h4 : 4 * ExcRaw.orthCount m c = 3024 := by
          rw [← hOP]
          exact h2''
        omega
      rw [hkind, if_neg hni, hA, h8, hc36, ho]
      norm_num [componentLabel, ExcRaw.labelSL]
    ·
      have hle7 : compRank Ψ ≤ 7 := by omega
      interval_cases hr : compRank Ψ <;>
        (have hni : ¬ twistInner Ψ (fun γ => -γ) := by
           rw [twistInner_neg_iff hτ' hΨ hne, hr, hA]
           norm_num
         rw [hkind, if_neg hni, hcA, hA]
         norm_num [componentLabel, ExcRaw.labelSL])
  ·
    have hcD : c.card = Ψ.ncard / 2 :=
      Nat.eq_div_of_mul_eq_right (by norm_num) hN.symm
    interval_cases hr : compRank Ψ
    ·
      have hneg : twistInner Ψ (fun γ => -γ) := by
        rw [twistInner_neg_iff hτ' hΨ hne, hr]
        exact Or.inr (Or.inl ⟨by omega, by norm_num, by omega⟩)
      rw [hkind, if_pos hneg, hcD, hD]
      norm_num [componentLabel, ExcRaw.labelSL]
    ·
      have hni : ¬ twistInner Ψ (fun γ => -γ) := by
        rw [twistInner_neg_iff hτ' hΨ hne, hr, hD]
        norm_num
      rw [hkind, if_neg hni, hcD, hD]
      norm_num [componentLabel, ExcRaw.labelSL]
    ·
      have hneg : twistInner Ψ (fun γ => -γ) := by
        rw [twistInner_neg_iff hτ' hΨ hne, hr]
        exact Or.inr (Or.inl ⟨by omega, by norm_num, by omega⟩)
      rw [hkind, if_pos hneg, hcD, hD]
      norm_num [componentLabel, ExcRaw.labelSL]
    ·
      have hni : ¬ twistInner Ψ (fun γ => -γ) := by
        rw [twistInner_neg_iff hτ' hΨ hne, hr, hD]
        norm_num
      rw [hkind, if_neg hni, hcD, hD]
      norm_num [componentLabel, ExcRaw.labelSL]
    ·
      have hneg : twistInner Ψ (fun γ => -γ) := by
        rw [twistInner_neg_iff hτ' hΨ hne, hr]
        exact Or.inr (Or.inl ⟨by omega, by norm_num, by omega⟩)
      rw [hkind, if_pos hneg, hcD, hD]
      norm_num [componentLabel, ExcRaw.labelSL]
  ·
    have hc6 : c.card = 36 := by omega
    have hni : ¬ twistInner Ψ (fun γ => -γ) := by
      rw [twistInner_neg_iff hτ' hΨ hne, h6, h72]
      norm_num
    have ho : ExcRaw.orthCount m c = 540 := by
      have h2'' := ncard_orthPairs_of_ncard_eq_seventyTwo hτ' hΨ h72
      rw [h6] at h2''
      simp at h2''
      have h4 : 4 * ExcRaw.orthCount m c = 2160 := by
        rw [← hOP]
        exact h2''
      omega
    rw [hkind, if_neg hni, h6, h72, hc6, ho]
    norm_num [componentLabel, ExcRaw.labelSL]
  ·
    have hneg : twistInner Ψ (fun γ => -γ) :=
      (twistInner_neg_iff hτ' hΨ hne).2 (Or.inr (Or.inr (Or.inl ⟨h7, h126⟩)))
    have hc7 : c.card = 63 := by omega
    rw [hkind, if_pos hneg, h7, h126, hc7]
    norm_num [componentLabel, ExcRaw.labelSL]
  ·
    have hneg : twistInner Ψ (fun γ => -γ) :=
      (twistInner_neg_iff hτ' hΨ hne).2 (Or.inr (Or.inr (Or.inr ⟨h8, h240⟩)))
    have hc8 : c.card = 120 := by omega
    rw [hkind, if_pos hneg, h8, h240, hc8]
    norm_num [componentLabel, ExcRaw.labelSL]

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
