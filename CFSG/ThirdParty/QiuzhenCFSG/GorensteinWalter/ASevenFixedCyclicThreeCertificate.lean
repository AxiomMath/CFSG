module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
public theorem a7_fixed_cyclic_three_certificate :
    ∀ x : ASevenCertificateGroup,
      (x ≠ 1 ∧ x ^ 3 = 1 ∧
        fixedSpanPow 3 x (a7v * x * a7v⁻¹)) →
      a7t * x = x * a7t := by
  unfold fixedSpanPow
  intro x hx
  rcases hx with ⟨hxne, hxpow, i, hi⟩
  have hv2 : a7v ^ 2 = a7t := by decide
  have hvpow : a7v * x ^ (i : Nat) * a7v⁻¹ =
      (a7v * x * a7v⁻¹) ^ (i : Nat) := by
    simpa using (map_pow (MulAut.conj a7v) x (i : Nat))
  have hv2x : a7v ^ 2 * x * (a7v ^ 2)⁻¹ =
      (x ^ (i : Nat)) ^ (i : Nat) := by
    calc
      a7v ^ 2 * x * (a7v ^ 2)⁻¹ =
          a7v * (a7v * x * a7v⁻¹) * a7v⁻¹ := by
        simp only [pow_two]
        group
      _ = a7v * x ^ (i : Nat) * a7v⁻¹ := by rw [hi]
      _ = (a7v * x * a7v⁻¹) ^ (i : Nat) := hvpow
      _ = (x ^ (i : Nat)) ^ (i : Nat) := by rw [hi]
  have htconj : a7t * x * a7t⁻¹ = x := by
    rw [← hv2]
    fin_cases i
    · exfalso
      apply hxne
      apply (MulAut.conj a7v).injective
      simpa using hi
    · simpa using hv2x
    · calc
        a7v ^ 2 * x * (a7v ^ 2)⁻¹ = (x ^ 2) ^ 2 := hv2x
        _ = x ^ 3 * x := by group
        _ = x := by rw [hxpow, one_mul]
  calc
    a7t * x = (a7t * x * a7t⁻¹) * a7t := by group
    _ = x * a7t := by rw [htconj]

end CFSG.GorensteinWalter
