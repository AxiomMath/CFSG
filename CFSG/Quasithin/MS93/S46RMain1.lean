module

public import CFSG.Quasithin.MS93.S46R466
public import CFSG.Quasithin.MS93.S46End
public import CFSG.Quasithin.MS93.S46Last
public import CFSG.Quasithin.MS93.S46I4612K
public import CFSG.Quasithin.MS93.S46I4612
public import CFSG.Quasithin.MS93.S46IdxLin
public import CFSG.Quasithin.MS93.S46I469
public import CFSG.Quasithin.MS93.S46I466b
public import CFSG.Quasithin.MS93.S46I466a
public import CFSG.Quasithin.MS93.S46I466aQ4
public import CFSG.Quasithin.MS93.S46I467
public import CFSG.Quasithin.MS93.S46I465
public import CFSG.Quasithin.MS93.S46I464
public import CFSG.Quasithin.MS93.S46I463
public import CFSG.Quasithin.MS93.S46I462
public import CFSG.Quasithin.MS93.S46I461
public import CFSG.Quasithin.MS93.S46KCTwo
public import CFSG.Quasithin.MS93.S46KCF
public import CFSG.Quasithin.MS93.S46I467T
public import CFSG.Quasithin.MS93.S468Red
public import CFSG.Quasithin.MS93.S46KC2Lin
public import CFSG.Quasithin.MS93.S46KCT
public import CFSG.Quasithin.MS93.S46Inputs
public import CFSG.Quasithin.MS93.S46I466aQPt

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.MS93.S46

theorem s46_of_one (h32 : S32) (h39 : S39) (h42 : S42) (h43 : S43) (h14 : MS14AS)
    (hSQ : SQTKQuot) (h468 : S468) : S46 := by
  have h461 := i461_of h32 h39 h43 h14 hSQ
  have h462 := i462_of h39 h461 h14 hSQ
  have h463 := i463_of h32 h39 h462
  have h464 := i464_of h42 h461 h462 h463 h14 hSQ
  have h465 := i465_of h43 h462 h463 h464
  have h466a := i466a_of (s466aQ4_of_orbit h14 hSQ h43 h462 h463 h464 h465) h464 h465
  have h466b := i466b_of h43 h461 h462 h463 h464 h465 h466a
  have h467 := i467_of_transv h461 h463 h464 h465 h466a
  have h469 := i469_of_s468 h43 h463 h464 h465 h466a h466b h467 h468
  have hKC2 := kc4612Two_of_i469 h463 h464 h465 h466b h467 h469
  have hidx := idx4612_of_kc2 hKC2 h14 hSQ h43 h463 h464 h465 h466a h466b h467 h469
  have hkc := kc4612_of_kc2 hKC2 h43 h463 h464 h465 h466a h466b h467 h469
  have h4612 := i4612_of hkc hidx h14 hSQ h43 h463 h464 h465 h466a h466b h467 h469
  have h46t := i46t_of h14 hSQ h463 h464 h465 h466a h466b h467 h469 h4612
  exact s46_of_parts h465 h466a (i46s_of_i46t h14 hSQ h463 h465 h466b h467 h46t)

end CFSG.Quasithin.MS93.S46R
