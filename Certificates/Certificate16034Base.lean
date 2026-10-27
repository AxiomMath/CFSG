
module

public import CFSG.Monster.Existence.TwoPoint.GammaExclData
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.AxisCount.Abstract
public import CFSG.Monster.Griess.Short
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Certificate1012Base
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL

@[expose] public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

namespace CertificateChecks.Batch16034

private theorem gx_square_mem_rels_0 : ∀ i < 10, [(i, true), (i, true)] ∈ rels := by
  decide +kernel

end CertificateChecks.Batch16034

namespace Certificates

end Certificates
