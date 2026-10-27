module

public import CFSG.Monster.GMS.Fi23GenTheta
public import CFSG.Monster.GMS.Fi23LocalBasic
public import CFSG.Sporadic.Fi23.Centralizer

public section

namespace CFSG.Monster.GMS.Fi23Gen

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.Fi23Local
open CFSG.Sporadic.Fi23 (J d D23)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.Monster.GMS.Fi23Gen

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.Fi23Local
open CFSG.Sporadic.Fi23 (J D23)
open CFSG.Blueprint.Fischer (LocalClass)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.Monster.GMS
