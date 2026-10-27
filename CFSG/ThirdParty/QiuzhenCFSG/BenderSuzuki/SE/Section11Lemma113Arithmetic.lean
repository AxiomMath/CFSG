module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_6

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.3: prime-power arithmetic

The Mersenne-power endpoint in the disjoint branch is an internal arithmetic
consequence of the checked prime-power successor trichotomy.  It is kept in a
small module so the group-theoretic branch does not need to import the whole
Peterfalvi claim file directly.
-/

namespace CFSG.BenderSuzuki

open PFchapter2

/-- If an odd prime power is one less than a positive power of `2`, the
successor exponent of the odd prime power is `1`.  In the Lemma 11.3
specialization this says `a = 0` from `r^(a+1) = 2^b - 1`. -/
public theorem lemma113_prime_power_successor_forces_exponent_zero
    {r a b : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hpow : r ^ (a + 1) = 2 ^ b - 1) :
    a = 0 := by
  have hb : 0 < b := by
    by_contra hb
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
    have hrpos : 0 < r ^ (a + 1) := pow_pos hr.pos _
    rw [hb0] at hpow
    simp only [pow_zero, Nat.sub_self] at hpow
    omega
  have hsucc : 2 ^ b = r ^ (a + 1) + 1 := by
    have htwo_pos : 0 < 2 ^ b := pow_pos (by omega) _
    rw [hpow]
    omega
  rcases PFchapter2.prime_power_successor_trichotomy
      Nat.prime_two hr hb (by omega) hsucc with
    hMersenne | hFermat | hNine
  · omega
  · exact False.elim (hr2 hFermat.1)
  · have hEven : Even (2 ^ b) :=
      Nat.even_pow.mpr ⟨even_two, hb.ne'⟩
    rw [hNine.1] at hEven
    rcases hEven with ⟨k, hk⟩
    omega

end CFSG.BenderSuzuki
