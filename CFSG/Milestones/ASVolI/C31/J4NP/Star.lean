module

public import Certificates.Certificate7851
public import CFSG.Milestones.ASVolI.C31.J4NP.Lemma9

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc (omegaZ)

theorem burnsideJ4NP_starProp : burnsideJ4NP_StarProp :=
  Certificates.certificate7851

variable {R : Subgroup J}

theorem burnsideJ4NP_maxNonParabolicP0_of_openReachP
    (h : burnsideJ4NP_OpenReachP) :
    burnsideJ4KW_MaxNonParabolicP0 :=
  burnsideJ4NP_maxNonParabolicP0_of_openReachP_of_star burnsideJ4NP_starProp h

end CFSG.ASVolI
