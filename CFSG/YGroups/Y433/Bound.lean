module

public import Certificates.Certificate10104

public section

namespace CFSG.YGroups

theorem B433_finite_card_le :
    Finite B433 ∧ Nat.card B433 ≤ 4154781481226426191177580544000000 :=
  Certificates.certificate10104

theorem Q343_finite_card_le :
    Finite Q343 ∧ Nat.card Q343 ≤ Q343N :=
  Q343_bound_of_B433 ⟨B433_finite_card_le.1, B433_finite_card_le.2.trans (by unfold Q343N; norm_num)⟩

end CFSG.YGroups
