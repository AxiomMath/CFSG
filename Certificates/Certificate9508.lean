module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24SevenData
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.LocalCompCubPartsSound
import Certificates.Kernel.LocalComp.F3.Fi24Sylow7H
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3 CFSG.AGLEmbedding.SporCubic

open CFSG.SectionRank.Native CFSG.AGLEmbedding.SporCubic in
theorem certificate9508 : ((ops3 781).cubicCheck fi24Sylow7HData = true) :=
  CFSG.KC.LocalComp.CubParts.cubicCheck_of_parts Fi24Sylow7H.lay_ok rfl rfl
    Fi24Sylow7H.LA_eq Fi24Sylow7H.LB_eq
    Fi24Sylow7H.decA Fi24Sylow7H.decB Fi24Sylow7H.one Fi24Sylow7H.steps Fi24Sylow7H.replay
    Fi24Sylow7H.parts Fi24Sylow7H.vt0 Fi24Sylow7H.vtab (by decide) Fi24Sylow7H.sort

end Certificates
