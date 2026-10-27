module

import Certificates.Kernel.LocalQT.Pipe.G7028
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2CheckInputs

public section

namespace Certificates

open CFSG in
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm in
theorem certificate7028 :
    (List.range j2Data.xs.size).all (fun h => blkSize 4725 (j2Blocks.getD h #[]) == 1 ||
      blkSize 4725 (j2Blocks.getD h #[]) % 3 == 0) = true :=
  CFSG.QuasithinUnique.Setup.X1.j2_block_sizes

end Certificates
