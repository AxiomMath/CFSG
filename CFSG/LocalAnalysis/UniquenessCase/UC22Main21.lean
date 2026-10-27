module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main14
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

structure Global22g : Prop extends Global22e where
  griess : CFSG.Open.GriessAllModelsStatement
  nativeGriess : uc22p20rNativeGriess
  excl : uc22p20oExclWitness
  two : uc22p20oTwoWitness

end CFSG.LocalAnalysis.UniquenessCase.UC22
