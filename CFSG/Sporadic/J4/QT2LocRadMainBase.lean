
module

public import CFSG.Sporadic.J4.QTProof

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem card_Cz_factorization_five (hC : Nat.card ↥(Subgroup.centralizer
    ({eta uJ 11 1131} : Set J)) = 21799895040) :
    (Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J))).factorization 5 = 1 := by
  rw [hC]
  have h : (21799895040 : ℕ) = 5 * 4359979008 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num : Nat.Prime 5),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.Sporadic.J4.QT2
