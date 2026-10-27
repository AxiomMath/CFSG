module

public import CFSG.GH74.GLS.C3.Layer1.St1P41M12Data
meta import CFSG.GH74.GLS.C3.Layer1.St1P41M12Data

public section

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.GH74.GLS.C3.Layer1.PumpElim

namespace Certificates

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.GH74.GLS.C3.Layer1.PumpElim in
theorem certificate5152 : evalCodes [m12gA, m12gB] wordJ = permJ ∧ permJ * permJ = 1 ∧ permJ * permZ = permZ * permJ ∧
    permJ ≠ permZ ∧ (Finset.univ.filter fun i : Fin 12 => permJ i = i).card = 0 ∧
    (Finset.univ.filter fun i : Fin 12 => (permZ * permJ) i = i).card = 0 :=
  by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Certificates
