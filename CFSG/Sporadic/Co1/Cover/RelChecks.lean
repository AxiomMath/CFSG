module

public import CFSG.Sporadic.Co1.Cover.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate10063
public meta import CFSG.Sporadic.Co1.Cover.Data
public meta import CFSG.Sporadic.Co1.Module.OddProg
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.OddNative
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.CoverCheck
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Sporadic.Co1.Module.InvDataBase
public import CFSG.Sporadic.Co1.Module.InvRepsBase
public meta import CFSG.Sporadic.Co1.Module.InvRepsBase

public section

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.CoverNative

theorem rel24_ok :
    relCheckAB 24 (rrCov 4) (rrCov 5) (invRows (rrCov 4)) (invRows (rrCov 5))
    TauCeti.SporadicName.M24.presentation.relatorLetters = true :=
  Certificates.certificate10063.1

theorem rel11_ok : relCheckAB 11 Aa Ba Aa (mulRows 11 Ba Ba)
    TauCeti.SporadicName.M24.presentation.relatorLetters = true :=
  Certificates.certificate10063.2.1

theorem noncomm_ok :
    CFSG.Sporadic.SmallF2.rowsMatrix 24 (mulRows 24 (rrCov 4) (rrCov 5)) ≠
    CFSG.Sporadic.SmallF2.rowsMatrix 24 (mulRows 24 (rrCov 5) (rrCov 4)) :=
  Certificates.certificate10063.2.2

end CFSG.Sporadic.Co1.Cover
