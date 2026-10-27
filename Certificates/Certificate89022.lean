module

public import Certificates.Data.CFSGNative.AS91.M24Duad
import CFSG.Certificates.Kernel.M24G.DuadSound
import Certificates.Kernel.M24G.DuadChecks
import Certificates.Kernel.M24G.ListsEq

public section

namespace Certificates

open CFSG.KC.M24G CFSG.KC.M24G.DuadC CFSG.Quasithin.H13.AS91.M24G
open scoped CFSG.KC.M24G.FixOctEq

theorem certificate89022 : CFSG.Quasithin.H13.AS91.M24G.Native.duadCheck () = true := by
  unfold Native.duadCheck
  rw [duadCoverCheck_of sextList_eq cover_ok, duadPairOrbitCheck_of pair_ok pairLen_ok,
    duadGrpCheck_of gens_ok.1 a_ok aLen_ok aInv_ok, duadEaCheck_of a_ok aLen_ok aEa_ok,
    duadGrpCheck_of gens_ok.2.1 b_ok bLen_ok bInv_ok, duadEaCheck_of b_ok bLen_ok bEa_ok,
    duadGrpCheck_of gens_ok.2.2 c_ok cLen_ok cInv_ok, s2_ok, sat_ok]
  rfl

end Certificates
