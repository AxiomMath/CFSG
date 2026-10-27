module

public import CFSG.Monster.GMS.Fi23GenTheta
public import CFSG.Monster.GMS.Fi23LocalBasic
public import CFSG.Sporadic.Fi23.InvCoverBase

public section

namespace CFSG.Monster.GMS.Fi23Gen

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Blueprint.Fischer CFSG.Monster.GMS.Fi23Local
open CFSG.Sporadic.Fi23 (J d d1 D23 d1_mem_localClass conj_mem_D23 fi23EquivJ isConj_symm_iff
  pair_J)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.Monster.GMS.Fi23Gen
