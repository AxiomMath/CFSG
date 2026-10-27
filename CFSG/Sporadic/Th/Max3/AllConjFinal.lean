module

public import CFSG.Sporadic.Th.Certificate
public import Certificates.Certificate9013

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th

theorem natCard_J :
    Nat.card J = 90745943887872000 :=
  Kernel.card_J_eq th_kernel_facts

theorem natCard_J_9013 :
    Nat.card J = 90745943887872000 :=
  Certificates.certificate9013

theorem all_involutions_conjugate :
    ∀ u : J, orderOf u = 2 → IsConj a u :=
  all_involutions_conjugate_of_card natCard_J

theorem th_involutions_conjugate :
    ∀ u : Blueprint.NativeSporadic.Th, orderOf u = 2 → IsConj (thEquivJ.symm a) u :=
  th_involutions_conjugate_of_card (by rw [Nat.card_congr thEquivJ.toEquiv]; exact natCard_J)

theorem th_involutions_isConj
    {u v : Blueprint.NativeSporadic.Th} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : IsConj u v :=
  (th_involutions_conjugate u hu).symm.trans (th_involutions_conjugate v hv)

end CFSG.Sporadic.Th.Max3
