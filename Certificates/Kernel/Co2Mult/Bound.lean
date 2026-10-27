module

public import CFSG.Sporadic.Recognition.Co2MultiplierInputs
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import Certificates.Kernel.Co2Cover.TabsA
import Certificates.Kernel.Co2Mult.Rels

public section

namespace CertificateChecks.KernelCo2Mult

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers
  CFSG.Sporadic.Recognition.Co2Multiplier

theorem cover_index :
    (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 47104 := by
  have words_eq : CFSG.KBRoute.F24011a.T1.words =
      (subsetOf 7 [0, 1, 2, 3, 4, 5]).map fun x => [(x.val, true)] := by decide +kernel
  have h := CFSG.KBFact.F24011a
  rw [← co2Cover_enc, words_eq] at h
  exact TableFact.genSub_index co2Cover (by norm_num) _ h

end CertificateChecks.KernelCo2Mult

end
