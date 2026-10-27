module

public import CFSG.Quasithin.H13.NQBlockRootHolds
public import CFSG.Quasithin.H13.NQCoreRadicalEscape

public section

namespace CFSG.Quasithin.H13.NQBlock

theorem stmtOriginalWitnessSingleton_holds :
    NQCore.StmtOriginalWitnessSingleton := by
  intro G _ _ T L M h p X hp hp5 hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr
  exact original_characteristic_witness_singleton_holds h hp hp5 hXR hXc hX2 hXno hXA hexp hrk hW
    hLW hirr

end CFSG.Quasithin.H13.NQBlock
