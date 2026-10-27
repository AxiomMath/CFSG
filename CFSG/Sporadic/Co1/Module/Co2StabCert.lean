module

public import CFSG.Sporadic.Co1.Module.Co2StabLit
public import Certificates.Certificate10064

public section

namespace CFSG.Sporadic.Co1.Module.Co2Stab

open CFSG.Blueprint

theorem eq_bot_of_normal_two_subgroup
    {v : Vec24} {c : NativeSporadic.Co1}
    (hc : co1Act c v₂ = v) {m : ℕ} (hm : Odd m) (hcard : Nat.card ↥(stabOf v) = 2 ^ 18 * m)
    {H N : Subgroup NativeSporadic.Co1} (hHC : H ≤ stabOf v)
    (hidx : Nat.card ↥(stabOf v) ≤ 2 * Nat.card ↥H) (hNH : N ≤ H)
    (hNnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hNp : IsPGroup 2 N) : N = ⊥ :=
  eq_bot_lit Certificates.certificate10064 hc hm hcard hHC hidx hNH hNnorm hNp

end CFSG.Sporadic.Co1.Module.Co2Stab
