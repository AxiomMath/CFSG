module

public import Certificates.Data.Kernel.CoverCK
public import Certificates.Data.CoverCenterThreeMcL
public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.CoverCenter.Masks
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.CoverMcL 3 21
  CFSG.Blueprint.NativeSporadic.McLSeed1 CFSG.Blueprint.NativeSporadic.McLSeed2

public section

namespace CFSG.KD.CoverMcL

open CFSG.KC.CoverCK CFSG.SectionRank.Native

theorem cover_K : coverKL lay A B mclCoverData = true := by decide +kernel

theorem orbit_K : coverOrbitKL lay A B mclCoverData 7 0 CFSG.KD.CoverMasks.mcl = true := by
  decide +kernel

def mclBadRel : CoverData 7 := { mclCoverData with rels := [[(0, true)]] }

theorem cover_neg : coverKL lay A B mclBadRel = false := by decide +kernel

def mclBad : CoverData 7 := { mclCoverData with gens := [19, 19, 40, 46, 52, 58, 72] }

theorem orbit_neg : coverOrbitKL lay A B mclBad 7 0 [3, 0, 0] = false := by
  decide +kernel

end CFSG.KD.CoverMcL

end
