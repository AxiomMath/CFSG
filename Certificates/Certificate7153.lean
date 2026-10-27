
module

public import CFSG.Quasithin.Vol2.KGFactU35Defs
import CFSG.Quasithin.Vol2.KGFactU35StarBase
import CFSG.Certificates.Kernel.C7153.Sound
import Certificates.Kernel.C7153.Check
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

open CFSG.Quasithin.H13.KGU35 CFSG.RankThree.PartOne.HNB CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.Classical Matrix

namespace Certificates

open CFSG.Quasithin.H13.KGU35 CFSG.RankThree.PartOne.HNB CFSG.ClassicalGroups.UnitaryFlag in
open CFSG.RankThree.Classical in
theorem certificate7153 : ∀ y : unitarySU 5 1 F25 3, y ^ 5 = 1 → y ≠ 1 →
    y * unitaryInvT f25Data = unitaryInvT f25Data * y → Star5 y := by
  have hSU : ∀ {A : Matrix (Fin 3) (Fin 3) F25}, A.det = 1 → (A.map (· ^ 5))ᵀ * A = 1 →
      ∃ g : unitarySU 5 1 F25 3, suMat g = A := fun hd hu =>
    ⟨⟨GeneralLinearGroup.mkOfDetNeZero _ (by rw [hd]; exact one_ne_zero), mem_SU.mpr ⟨hd, hu⟩⟩,
      rfl⟩
  refine fun y hy5 hy1 hyt => ?_
  obtain ⟨hdet, hu⟩ := mem_SU.mp y.2
  have ht : suMat y * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * suMat y := by
    have := congrArg suMat hyt
    rwa [map_mul, map_mul, suMat_unitaryInvT, negNegOneDiag] at this
  have h5 : suMat y ^ 5 = 1 := by rw [← map_pow, hy5, map_one]
  have h1 : suMat y ≠ 1 := fun h => hy1 (suMat_injective (by rw [h, map_one]))
  obtain ⟨A, B, hA1, hA2, hB1, hB2, hAB, hAy, hBy, hA5, hB5⟩ :=
    CFSG.KC.C7153.c7153K_sound (M := suMat y) CFSG.KD.C7153.ch7153_ok hdet hu ht h5 h1
  obtain ⟨gA, hgA⟩ := hSU hA1 hA2
  obtain ⟨gB, hgB⟩ := hSU hB1 hB2
  exact CFSG.KC.C7153.star5_of_gens (y := y) (a := gA) (b := gB)
    (suMat_injective (by rw [map_mul, map_mul, map_mul, hgA, hgB]; exact hAB))
    (suMat_injective (by rw [map_mul, map_mul, hgA]; exact hAy))
    (suMat_injective (by rw [map_mul, map_mul, hgB]; exact hBy))
    (suMat_injective (by rw [map_pow, hgA, hA5, map_one]))
    (suMat_injective (by rw [map_pow, hgB, hB5, map_one])) hy5

end Certificates
