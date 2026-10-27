module

public import CFSG.Monster.GMS.S4CohBBasic
public import CFSG.Monster.GMS.S36LinesBasic
import CFSG.Monster.GMS.S57
import CFSG.Monster.GMS.S5Inputs
import CFSG.Monster.GMS.S31Three
import CFSG.Monster.GMS.NotConj
import CFSG.Monster.GMS.S341
import CFSG.Monster.GMS.S342
import CFSG.Monster.GMS.Coxeter
public import Certificates.Certificate3024

public section

namespace CFSG.Monster.GMS.S4CohB

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Family CFSG.Monster.GMS.S4Assembly
  CFSG.Monster.GMS.S4CohA CFSG.Monster.GMS.S36Lines

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

end CFSG.Monster.GMS.S4CohB
