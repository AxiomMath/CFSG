module

public import Certificates.Data.TabBThreeL1Levels
import Certificates.Kernel.TabBThreeL1.Levels
import CFSG.Certificates.Kernel.TabBThreeL1.LevelsSound

public section

open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

namespace Certificates

open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1 CFSG.Monster.B.Classical.E6Adjoint in
theorem certificate17579 : ∀ (R : Type) [CommRing R]
    [CharP R 2] (a b c : Fin 78),
    (bracket R (eLab R a) (eLab R b) (lab c) ≠ 0 → lev a + lev b = lev c + 2) ∧
      (form R (eLab R a) (eLab R b) ≠ 0 → lev a + lev b = 4) :=
  fun R _ _ a b c =>
    ⟨ch17575_bracket_lev ch17575_levMask
        (ch17575_gradedOK ch17575_graded_0 ch17575_graded_1 ch17575_graded_2) a b c,
      ch17575_form_lev (ch17575_gradedOK ch17575_graded_0 ch17575_graded_1 ch17575_graded_2) a b⟩

end Certificates
