module

public import Certificates.Certificate7410

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Sporadic.Schreier.Tits

theorem invTitsCheck_true : invTitsCheck () = true :=
  Certificates.certificate7410

theorem invTitsZCheck :
    invTitsClassCheck titsCenterWord invTitsZConjWord 5 5 = true := by
  have h := invTitsCheck_true
  rw [invTitsCheck, Bool.and_eq_true] at h
  exact h.1

theorem invTitsTCheck :
    invTitsClassCheck titsTWord invTitsTConjWord 13 13 = true := by
  have h := invTitsCheck_true
  rw [invTitsCheck, Bool.and_eq_true] at h
  exact h.2

end CFSG.Quasithin.F7Two
