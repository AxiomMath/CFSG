module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Coprimality of the two half-torus orders
-/

noncomputable section
namespace CFSG.GorensteinWalter

/-- For an odd natural number, each of the two half-torus orders is coprime
with the field order itself. -/
public theorem secondCase_linear_half_coprime_of_odd
    {q : ℕ} (hqodd : Odd q) :
    Nat.Coprime ((q - 1) / 2) q ∧ Nat.Coprime ((q + 1) / 2) q := by
  constructor
  · apply Nat.coprime_of_dvd
    intro p hp hpdvd hpdvdq
    have h2 : 2 ∣ q - 1 := by
      rcases hqodd with ⟨a, ha⟩
      use a
      omega
    have hpdvdq1 : p ∣ q - 1 := by
      rcases hpdvd with ⟨k, hk⟩
      refine ⟨2 * k, ?_⟩
      calc
        q - 1 = ((q - 1) / 2) * 2 := (Nat.div_mul_cancel h2).symm
        _ = (p * k) * 2 := by rw [hk]
        _ = p * (2 * k) := by ring
    have hpdvd1 : p ∣ 1 := by
      have hdiv := Nat.dvd_sub hpdvdq hpdvdq1
      have hqpos : 0 < q := hqodd.pos
      have hsub : q - (q - 1) = 1 := by omega
      rwa [hsub] at hdiv
    exact hp.not_dvd_one hpdvd1
  · apply Nat.coprime_of_dvd
    intro p hp hpdvd hpdvdq
    have h2 : 2 ∣ q + 1 := by
      rcases hqodd with ⟨a, ha⟩
      use a + 1
      omega
    have hpdvdq1 : p ∣ q + 1 := by
      rcases hpdvd with ⟨k, hk⟩
      refine ⟨2 * k, ?_⟩
      calc
        q + 1 = ((q + 1) / 2) * 2 := (Nat.div_mul_cancel h2).symm
        _ = (p * k) * 2 := by rw [hk]
        _ = p * (2 * k) := by ring
    have hpdvd1 : p ∣ 1 := by
      have hdiv := Nat.dvd_sub hpdvdq1 hpdvdq
      have hqpos : 0 < q := hqodd.pos
      have hsub : q + 1 - q = 1 := by omega
      rwa [hsub] at hdiv
    exact hp.not_dvd_one hpdvd1

end CFSG.GorensteinWalter
