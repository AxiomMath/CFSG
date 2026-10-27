module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporB
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo1
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo3
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporFi22
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporFi23
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporFi24
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporHN
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporJ
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporJ3
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporJ4
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLatFour
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLy
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporM
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporM23
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporMcL
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporON
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporPerm
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporSuz
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporTh

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asch54SporGenAt_of_ne_th :
    ∀ s : TauCeti.SporadicName, s ≠ .Th → Asch54SporGenAt s
  | .M11, _ => asch54SporGenAt_m11
  | .M12, _ => asch54SporGenAt_m12
  | .M22, _ => asch54SporGenAt_m22
  | .M23, _ => asch54SporGenAt_m23
  | .M24, _ => asch54SporGenAt_m24
  | .J1, _ => asch54SporGenAt_j1
  | .J2, _ => asch54SporGenAt_j2
  | .J3, _ => asch54SporGenAt_j3
  | .J4, _ => asch54SporGenAt_j4
  | .HS, _ => asch54SporGenAt_hs
  | .McL, _ => asch54SporGenAt_mcl
  | .He, _ => asch54SporGenAt_he
  | .Ru, _ => asch54SporGenAt_ru
  | .Suz, _ => asch54SporGenAt_suz
  | .ONan, _ => asch54SporGenAt_onan
  | .Co1, _ => asch54SporGenAt_co1
  | .Co2, _ => asch54SporGenAt_co2
  | .Co3, _ => asch54SporGenAt_co3
  | .Fi22, _ => asch54SporGenAt_fi22
  | .Fi23, _ => asch54SporGenAt_fi23
  | .Fi24Prime, _ => asch54SporGenAt_fi24Prime
  | .HN, _ => asch54SporGenAt_hn
  | .Ly, _ => asch54SporGenAt_ly
  | .Th, h => absurd rfl h
  | .B, _ => asch54SporGenAt_b
  | .M, _ => asch54SporGenAt_m

theorem asch54Spor_holds :
    Asch54Spor :=
  asch54Spor_of_gen asch54SporGenAt_of_ne_th asch54SporThGen_holds

end CFSG.LocalAnalysis.WeakClosure81

end
