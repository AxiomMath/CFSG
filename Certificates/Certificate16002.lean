module

public import CFSG.Monster.B.Final.Simple
public import CFSG.Monster.B.Rep4371.ExactActions
public import CFSG.Monster.B.Final.Max2Nodes
public import CFSG.Monster.B.Pinned.Primes.FiveSubgroup
public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import CFSG.Monster.B.Pinned.Primes.ThreeTwelve
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Bridge.BSeven
public import CFSG.Sporadic.Bridge.BOrderInputs

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.B CFSG.Blueprint CFSG.Monster.B
  CFSG.Monster.B.Pinned CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native
open scoped Matrix

namespace CertificateChecks.Batch16002

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.B CFSG.Blueprint CFSG.Monster.B
  CFSG.Monster.B.Pinned CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native
open scoped Matrix

private theorem w1_lt_0 : ∀ l ∈ w1, l.1 < 2 := by
  decide +kernel

private theorem w2_lt_1 : ∀ l ∈ w2, l.1 < 2 := by
  decide +kernel

private theorem rows_facts_2 :
    lpow (wordRows w1) 3 = lpow (wordRows w1) 0 ∧ lpow (wordRows w2) 3 = lpow (wordRows w2) 0 ∧
    lvecMul 3 8 orbitBase (wordRows w1) = orbitBase ∧
    lvecMul 3 8 orbitBase (wordRows w2) = orbitBase ∧
    lmul (wordRows w1) (wordRows w2) = lmul (wordRows w2) (wordRows w1) ∧
    rowsMat 3 8 (wordRows w1) ≠ 1 ∧ rowsMat 3 8 (wordRows w2) ≠ 1 ∧
    rowsMat 3 8 (wordRows w2) ≠ rowsMat 3 8 (wordRows w1) ∧
    rowsMat 3 8 (wordRows w2) ≠ rowsMat 3 8 (lpow (wordRows w1) 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

end CertificateChecks.Batch16002

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.B CFSG.Blueprint CFSG.Monster.B
  CFSG.Monster.B.Pinned CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native in
open scoped Matrix in
theorem certificate16002 : (
    ∀ l ∈ w1, l.1 < 2
  ) ∧ (
    ∀ l ∈ w2, l.1 < 2
  ) ∧ (
    lpow (wordRows w1) 3 = lpow (wordRows w1) 0 ∧ lpow (wordRows w2) 3 = lpow (wordRows w2) 0 ∧
    lvecMul 3 8 orbitBase (wordRows w1) = orbitBase ∧
    lvecMul 3 8 orbitBase (wordRows w2) = orbitBase ∧
    lmul (wordRows w1) (wordRows w2) = lmul (wordRows w2) (wordRows w1) ∧
    rowsMat 3 8 (wordRows w1) ≠ 1 ∧ rowsMat 3 8 (wordRows w2) ≠ 1 ∧
    rowsMat 3 8 (wordRows w2) ≠ rowsMat 3 8 (wordRows w1) ∧
    rowsMat 3 8 (wordRows w2) ≠ rowsMat 3 8 (lpow (wordRows w1) 2)
  ) := by
  exact ⟨CertificateChecks.Batch16002.w1_lt_0, CertificateChecks.Batch16002.w2_lt_1, CertificateChecks.Batch16002.rows_facts_2⟩

end Certificates
