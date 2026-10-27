module

public import CFSG.Quasithin.MS93.S46RMain1
public import CFSG.Quasithin.MS93.S46R468Main

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.MS93.S46

theorem s46_of_deg (h32 : S32) (h39 : S39) (h42 : S42) (h43 : S43) (h14 : MS14AS)
    (hSQ : SQTKQuot) (hDeg : S468Deg) : S46 := by
  have h461 := i461_of h32 h39 h43 h14 hSQ
  have h462 := i462_of h39 h461 h14 hSQ
  have h463 := i463_of h32 h39 h462
  have h464 := i464_of h42 h461 h462 h463 h14 hSQ
  have h465 := i465_of h43 h462 h463 h464
  have h466a := i466a_of (s466aQ4_of_orbit h14 hSQ h43 h462 h463 h464 h465) h464 h465
  have h467 := i467_of_transv h461 h463 h464 h465 h466a
  exact s46_of_one h32 h39 h42 h43 h14 hSQ (s468_of h43 h463 h464 h465 h466a h467 hDeg)

end CFSG.Quasithin.MS93.S46R
