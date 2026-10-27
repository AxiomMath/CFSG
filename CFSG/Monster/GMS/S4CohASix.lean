module

public import CFSG.Monster.GMS.S4CohAFourA
public import CFSG.Monster.GMS.S46Basic
public import Certificates.Certificate3024

public section

namespace CFSG.Monster.GMS.S4CohA

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Family CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

end CFSG.Monster.GMS.S4CohA
