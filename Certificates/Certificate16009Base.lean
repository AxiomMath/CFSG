
module

import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.AxisCount.Abstract
public import CFSG.Monster.B.Short.Rootless
public import CFSG.Monster.Existence.TwoPoint.Fi23Data
public import CFSG.Monster.Generated.Data
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Certificate1012Base
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL

@[expose] public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

namespace CertificateChecks.Batch16009

private theorem fiRels_lt_0 : ∀ v ∈ rels, ∀ l ∈ v, l.1 < 10 := by
  decide +kernel

private theorem fiRels_pos_1 : ∀ v ∈ rels, ∀ l ∈ v, l.2 = true := by
  decide +kernel

end CertificateChecks.Batch16009

namespace Certificates

end Certificates
