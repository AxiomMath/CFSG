module

public import Certificates.Data.TabBThreeL1Levels
import Certificates.Kernel.TabBThreeL1.Levels
import CFSG.Certificates.Kernel.TabBThreeL1.LevelsSound

public section

open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

namespace Certificates

open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1 CFSG.Monster.B.Classical.E6Adjoint in
open CFSG.Blueprint.Chevalley in
theorem certificate17580 : ∀ (R : Type) [CommRing R]
    [CharP R 2] (y : RootModule Tag.E6 R), xOne R (eLab R 76) (xOne R (eLab R 77) y) = y →
      ∀ k : Fin 78, lev k = 1 → y (lab k) = 0 :=
  fun R _ _ y hz => ch17575_fixed_lev ch17575_levMask
    (ch17575_gradedOK ch17575_graded_0 ch17575_graded_1 ch17575_graded_2) ch17575_lev_theta
    ch17575_piv_theta y hz

end Certificates
