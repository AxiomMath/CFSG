module

public import CFSG.Monster.GMS.S4FamilyIso
public import CFSG.Monster.GMS.S4FamilyDefs
public import CFSG.Monster.GMS.Facts.Section4

public section

namespace CFSG.Monster.GMS.S4Family

open CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

end CFSG.Monster.GMS.S4Family
