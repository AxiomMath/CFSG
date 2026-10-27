module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BSpor

import CFSG.LocalAnalysis.WeakClosure81.Asc80BSporTh
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo1
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporFi23
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporM23
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporJ4
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLatFour
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLy
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporFi22
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporB
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporJ
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporPerm
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporON
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo3
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporMcL
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporFi24
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporJ3
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporSuz
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporM
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporHN

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asc80ThmBCase_sporadic :
    Asc80ThmBCase fun X _ => CFSG.Models.SporadicRep X := by
  refine asc80ThmBCase_sporadicRep_of_noUMax fun s hs => asc80NoUMax_of_sporGenAt ?_
  cases s with
  | M11 => exact asch54SporGenAt_m11
  | M12 => exact asch54SporGenAt_m12
  | M22 => exact asch54SporGenAt_m22
  | M23 => exact asch54SporGenAt_m23
  | M24 => exact asch54SporGenAt_m24
  | J1 => exact asch54SporGenAt_j1
  | J2 => exact asch54SporGenAt_j2
  | J3 => exact asch54SporGenAt_j3
  | J4 => exact asch54SporGenAt_j4
  | HS => exact asch54SporGenAt_hs
  | McL => exact asch54SporGenAt_mcl
  | Suz => exact asch54SporGenAt_suz
  | He => exact asch54SporGenAt_he
  | Ly => exact asch54SporGenAt_ly
  | Ru => exact asch54SporGenAt_ru
  | ONan => exact asch54SporGenAt_onan
  | Co1 => exact asch54SporGenAt_co1
  | Co2 => exact asch54SporGenAt_co2
  | Co3 => exact asch54SporGenAt_co3
  | Fi22 => exact asch54SporGenAt_fi22
  | Fi23 => exact asch54SporGenAt_fi23
  | Fi24Prime => exact asch54SporGenAt_fi24Prime
  | B => exact asch54SporGenAt_b
  | M => exact asch54SporGenAt_m
  | HN => exact asch54SporGenAt_hn
  | Th => exact absurd rfl hs

end CFSG.LocalAnalysis.WeakClosure81

end
