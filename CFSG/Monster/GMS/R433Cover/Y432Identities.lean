module

public import CFSG.Monster.GMS.R433Cover.Y432Transport
public import CFSG.YGroups.Exact.Y432
public import CFSG.Monster.GMS.R433Cover.Y432IdentitiesInputs
public import Certificates.Certificate10036
public meta import CFSG.Monster.GMS.R433Cover.Y432Transport
public meta import CFSG.YGroups.Defs
public meta import CFSG.YGroups.Exact.Y432
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.ExactData

public section

namespace CFSG.Monster.GMS.R433Cover

open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.YGroups (spiderWord yGen evalWord_yGen_432_eq_iff evalWord_yGen_432_eq_one_iff)

theorem yConj_length : yConj.length = 71 := by decide +kernel

theorem yConj_lt : ∀ c ∈ yConj, c < 10 := by decide +kernel

theorem y432_I1 :
    evalWord (yGen 4 3 2)
    (List.replicate 3 ((List.replicate 5 (spiderWord 4 3)).flatten ++ [0])).flatten = 1 := by
  rw [evalWord_yGen_432_eq_one_iff]
  exact Certificates.certificate10036.1

theorem y432_I2 :
    evalWord (yGen 4 3 2) (yConj.reverse ++ [0, 4, 6] ++ yConj) =
    evalWord (yGen 4 3 2) ([2, 5, 7, 9] ++ f213Word) := by
  rw [evalWord_yGen_432_eq_iff]
  exact Certificates.certificate10036.2

end CFSG.Monster.GMS.R433Cover
