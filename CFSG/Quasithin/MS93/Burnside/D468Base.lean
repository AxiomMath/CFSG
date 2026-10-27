module

public import CFSG.Quasithin.MS93.Burnside.D468Fin
public import CFSG.Quasithin.MS93.S46RMain3

public section

namespace CFSG.Yardstones.M71b2fd3d34b9

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46R

theorem burnsideD468_items_of_base (h32 : S32) (h43 : S43) (h14 : MS14AS) (hSQ : SQTKQuot) :
    I464 ∧ I465 ∧ I466a := by
  have h39 := s39_of h32
  have h42 := s42_of h32
  have h461 := i461_of h32 h39 h43 h14 hSQ
  have h462 := i462_of h39 h461 h14 hSQ
  have h463 := i463_of h32 h39 h462
  have h464 := i464_of h42 h461 h462 h463 h14 hSQ
  have h465 := i465_of h43 h462 h463 h464
  exact ⟨h464, h465, i466a_of (s466aQ4_of_orbit h14 hSQ h43 h462 h463 h464 h465) h464 h465⟩

theorem burnsideD468_s468DegN_of_base (h32 : S32) (h43 : S43) (h14 : MS14AS)
    (hSQ : SQTKQuot) : S46R.S468DegN :=
  have h := burnsideD468_items_of_base h32 h43 h14 hSQ
  burnsideD468_s468DegN_of_items h.1 h.2.1 h.2.2

theorem burnsideD468_s46_of_base (h32 : S32) (h43 : S43) (h14 : MS14AS) (hSQ : SQTKQuot) :
    S46 :=
  s46_of_degN h32 (s39_of h32) (s42_of h32) h43 h14 hSQ
    (burnsideD468_s468DegN_of_base h32 h43 h14 hSQ)

end CFSG.Yardstones.M71b2fd3d34b9
