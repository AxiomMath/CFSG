module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Check
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Check
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CosetNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import Certificates.Certificate7028

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm

theorem j2BlockSizes_check :
    (List.range j2Data.xs.size).all (fun h => blkSize 4725 (j2Blocks.getD h #[]) == 1 ||
      blkSize 4725 (j2Blocks.getD h #[]) % 3 == 0) = true :=
  Certificates.certificate7028

end CFSG.Quasithin.H13.QTESylow
