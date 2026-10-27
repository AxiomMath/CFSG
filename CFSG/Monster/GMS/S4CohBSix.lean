module

public import CFSG.Monster.GMS.S4CohBBasic
public import Certificates.Certificate3024

public section

namespace CFSG.Monster.GMS.S4CohB

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Family CFSG.Monster.GMS.S4Assembly
  CFSG.Monster.GMS.S36Lines

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

end CFSG.Monster.GMS.S4CohB
