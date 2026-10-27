module

public import CFSG.Monster.GMS.S4CohAGen
public import CFSG.Monster.GMS.S4CohAModify
public import CFSG.Monster.GMS.S4CohAClasses
public import CFSG.Monster.GMS.S4CohATrans
public import CFSG.Monster.GMS.S4FamilyGroup
public import CFSG.Monster.GMS.S46Basic
public import CFSG.Monster.GMS.S46A12
public import CFSG.Monster.GMS.Facts.Interfaces
import CFSG.Monster.GMS.NotConj
public import Certificates.Certificate3024

public section

namespace CFSG.Monster.GMS.S4CohA

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Family CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

end CFSG.Monster.GMS.S4CohA
