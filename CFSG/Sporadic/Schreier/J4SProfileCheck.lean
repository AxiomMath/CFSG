
module

public import CFSG.Sporadic.Schreier.J4SProfileCheckBase

public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
public import Certificates.Certificate2179
public import CFSG.Sporadic.Schreier.J4SFrattiniBase

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2

theorem kfun_lt : ∀ e < 1024, ∀ n < 2048, kfun n e < 5 :=
  Certificates.certificate2179.1

theorem profCount_eq : ∀ b < 32, ∀ j < 5, profCount b j = (profTable[b]!)[j]! :=
  Certificates.certificate2179.2.1

theorem ell_eq : ∀ n < 2048, ell n < 2 ∧ ellV (toVecD 11 n) = (ell n : ZMod 2) :=
  Certificates.certificate2179.2.2.1

theorem cons_toVecD_iff : ∀ b < 32, ∀ c < 16, ∀ x : ZMod 2,
    (Fin.cons x (toVecD 4 c) : Fin 5 → ZMod 2) = toVecD 5 b ↔
      x = ((b % 2 : ℕ) : ZMod 2) ∧ c = b / 2 :=
  Certificates.certificate2179.2.2.2.1

theorem profTable_unique :
    ∀ a ∈ [5, 6, 7, 8, 17], ∀ b < 32, profTable[b]! = profTable[a]! → b = a :=
  Certificates.certificate2179.2.2.2.2.1

theorem profTable_size : profTable.size = 32 ∧ ∀ b < 32, (profTable[b]!).size = 5 :=
  Certificates.certificate2179.2.2.2.2.2.1

theorem toVecD_five_surj : ∀ w : Fin 5 → ZMod 2, ∃ b < 32, toVecD 5 b = w :=
  Certificates.certificate2179.2.2.2.2.2.2.1

theorem basis_five_span : ∀ w : Fin 5 → ZMod 2, ∃ c : Fin 5 → ZMod 2,
    ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = w :=
  Certificates.certificate2179.2.2.2.2.2.2.2.1

theorem basis_five_indep : ∀ c : Fin 5 → ZMod 2,
    ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = 0 → c = 0 :=
  Certificates.certificate2179.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4Schreier
