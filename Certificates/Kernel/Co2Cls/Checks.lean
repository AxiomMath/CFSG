module

public import Certificates.Kernel.Co2Cls.Rec4a
public import Certificates.Kernel.Co2Cls.Rec4b
public import Certificates.Kernel.Co2Cls.Rec9a
public import Certificates.Kernel.Co2Cls.Rec9b
public import Certificates.Kernel.Co2Cls.Rec9c
public import Certificates.Kernel.Co2Cls.Rec9d
public import Certificates.Kernel.Co2Cls.Rec9e
public import Certificates.Kernel.Co2Cls.Rec9f
public import Certificates.Kernel.Co2Cls.Rec9g
public import Certificates.Kernel.Co2Cls.Rec9h
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2Cls CertificateChecks.KernelSpor.Co2Syl

theorem slice {F : Nat → Bool} {lo n : Nat} (h : ∀ t < n, F (Nat.add lo t) = true) :
    ∀ k, lo ≤ k → k < lo + n → F k = true := by
  intro k h1 h2
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [← e]
  exact h _ (by omega)

theorem recs4 : ∀ k < 22680, recC C4 GC 21 (RP 4) 22680 k = true := by
  intro k hk
  by_cases h : k < 16384
  · exact slice rec4a k (Nat.zero_le _) (by omega)
  · exact slice rec4b k (by omega) (by omega)

theorem recs9 : ∀ k < 120960, recC C9 GC 21 (RP 9) 120960 k = true := by
  intro k hk
  have s := fun (lo : Nat) (h : ∀ t < 16384, recC C9 GC 21 (RP 9) 120960 (Nat.add lo t) = true)
    (h1 : lo ≤ k) (h2 : k < lo + 16384) => slice h k h1 h2
  by_cases h1 : k < 16384
  · exact s 0 rec9a (Nat.zero_le _) (by omega)
  by_cases h2 : k < 32768
  · exact s 16384 rec9b (by omega) (by omega)
  by_cases h3 : k < 49152
  · exact s 32768 rec9c (by omega) (by omega)
  by_cases h4 : k < 65536
  · exact s 49152 rec9d (by omega) (by omega)
  by_cases h5 : k < 81920
  · exact s 65536 rec9e (by omega) (by omega)
  by_cases h6 : k < 98304
  · exact s 81920 rec9f (by omega) (by omega)
  by_cases h7 : k < 114688
  · exact s 98304 rec9g (by omega) (by omega)
  · exact slice rec9h k (by omega) (by omega)

end CertificateChecks.KernelSpor.Co2Cls

end
