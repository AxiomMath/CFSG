module

public import Certificates.Data.TabBThreeL1Levels
import Certificates.Kernel.TabBThreeL1.Levels
import CFSG.Certificates.Kernel.TabBThreeL1.LevelsSound

public section

open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

namespace Certificates

open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1 CFSG.Monster.B.Classical.E6Adjoint in
open CFSG.Blueprint.Chevalley in
theorem certificate17581 : ∀ (R : Type) [CommRing R]
    [CharP R 2],
    (∀ β k : Fin 78, (β : ℕ) ∈ [6, 8, 9, 33] → lev k = 1 →
      bracket R (eLab R β) (bracket R (eLab R β) (eLab R k)) = 0) ∧
    ∀ y : RootModule Tag.E6 R, (∀ k : Fin 78, lev k ≠ 1 → y (lab k) = 0) →
      (∀ β : Fin 78, (β : ℕ) ∈ [6, 8, 9, 33] → bracket R (eLab R β) y = 0) → y = 0 :=
  fun R _ _ => ⟨fun β k hβ hk => ch17575_adSq_test ch17575_adSq β k hβ hk,
    fun y hy hβ => ch17575_test_kernel ch17575_levMask ch17575_piv_test y hy hβ⟩

end Certificates
