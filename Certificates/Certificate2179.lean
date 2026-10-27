
module

public import Certificates.Certificate2179Base

public import CFSG.Sporadic.Schreier.J4SFrattiniBase
public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
import Certificates.Kernel.SporSch.J4S.Profile

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2 in
theorem certificate2179 : (∀ e < 1024, ∀ n < 2048, kfun n e < 5)
    ∧ (∀ b < 32, ∀ j < 5, profCount b j = (profTable[b]!)[j]!)
    ∧ (∀ n < 2048, ell n < 2 ∧ ellV (toVecD 11 n) = (ell n : ZMod 2))
    ∧ (∀ b < 32, ∀ c < 16, ∀ x : ZMod 2,
      (Fin.cons x (toVecD 4 c) : Fin 5 → ZMod 2) = toVecD 5 b ↔
        x = ((b % 2 : ℕ) : ZMod 2) ∧ c = b / 2
    )
    ∧ (∀ a ∈ [5, 6, 7, 8, 17], ∀ b < 32, profTable[b]! = profTable[a]! → b = a)
    ∧ (profTable.size = 32 ∧ ∀ b < 32, (profTable[b]!).size = 5)
    ∧ (∀ w : Fin 5 → ZMod 2, ∃ b < 32, toVecD 5 b = w)
    ∧ (∀ w : Fin 5 → ZMod 2, ∃ c : Fin 5 → ZMod 2,
      ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = w
    )
    ∧ (∀ c : Fin 5 → ZMod 2,
      ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = 0 → c = 0
    ) := KernelSporSch.J4Profile.facts

end Certificates
