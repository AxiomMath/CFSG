module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Inputs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
import Certificates.Kernel.D42.Glue

public section

namespace Certificates

open CFSG.EvenSmallLie.OmegaEight CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42 in
theorem certificate118001 :
    3 * (CFSG.Sporadic.Schreier.conjClass omegaT (mainPerm 1)).ncard ≤
        (CFSG.Sporadic.Schreier.conjClass autT (mainPerm 1)).ncard ∧
      ∀ j < 2, ∃ P U : Subgroup (Equiv.Perm (Fin 360)),
        P ≤ CFSG.Sporadic.Schreier.centralizerIn autT (mainPerm (mainIdx j)) ∧
        Nat.card P = pOrder j ∧ IsPGroup 2 U ∧ U ≤ omegaT ∧
        U ≤ Subgroup.centralizer ({mainPerm (mainIdx j)} : Set (Equiv.Perm (Fin 360))) ∧
        P ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 360))) ∧
        ∀ y ∈ P, y ≠ 1 → 9 ≤ Nat.card ↥⁅U, Subgroup.zpowers y⁆ :=
  CFSG.KD.D42.proof118001

end Certificates
