module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.Glauberman

universe u

/-- If every element whose order is prime to `p` lies in a normal subgroup `N`,
then `G/N` is a `p`-group.  For a lift `x` of a quotient element, raising `x` to
the full `p`-part of `orderOf x` produces a `p'`-element; killing that element in
the quotient forces the quotient order to divide a power of `p`. -/
public theorem isPGroup_quotient_of_pPrime_order_elements_mem
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hN : ∀ x : G, ¬ p ∣ orderOf x → x ∈ N) :
    IsPGroup p (G ⧸ N) := by
  classical
  rw [IsPGroup.iff_orderOf]
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
  let v : ℕ := padicValNat p (orderOf x)
  let a : ℕ := p ^ v
  have hord_ne : orderOf x ≠ 0 := ne_of_gt (orderOf_pos x)
  have ha_dvd : a ∣ orderOf x := by
    simpa [a, v] using (pow_padicValNat_dvd (p := p) (n := orderOf x))
  have horder_pow : orderOf (x ^ a) = orderOf x / a := by
    rw [orderOf_pow, Nat.gcd_eq_right_iff_dvd.mpr ha_dvd]
  have hp_not_dvd : ¬ p ∣ orderOf (x ^ a) := by
    rw [horder_pow]
    intro hp
    rcases hp with ⟨k, hk⟩
    have hfactor : a * (orderOf x / a) = orderOf x := Nat.mul_div_cancel' ha_dvd
    have hsucc_dvd : p ^ (v + 1) ∣ orderOf x := by
      refine ⟨k, ?_⟩
      calc
        orderOf x = a * (orderOf x / a) := hfactor.symm
        _ = p ^ v * (p * k) := by rw [hk]
        _ = p ^ (v + 1) * k := by rw [pow_succ, mul_assoc]
    have hv_succ : v + 1 ≤ padicValNat p (orderOf x) :=
      (padicValNat_dvd_iff_le hord_ne).mp hsucc_dvd
    simp [v] at hv_succ
  have hxpow_N : x ^ a ∈ N := hN (x ^ a) hp_not_dvd
  have hqpow : (QuotientGroup.mk' N x) ^ a = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := N) (x := x ^ a)).2 hxpow_N
  have hord_dvd : orderOf (QuotientGroup.mk' N x) ∣ p ^ v := by
    simpa [a] using (orderOf_dvd_iff_pow_eq_one.mpr hqpow)
  rcases (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hord_dvd with ⟨k, _hk, hk⟩
  exact ⟨k, hk⟩

end CFSG.Glauberman
