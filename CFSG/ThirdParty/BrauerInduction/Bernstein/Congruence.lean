module

public import CFSG.ThirdParty.BrauerInduction.Bernstein.PrimeToP
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.PrimePowerCongruence
public import CFSG.ThirdParty.BrauerInduction.Elementary.LocalSum

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Bernstein's congruences modulo prime powers

For each prime `p` and exponent `r`, this file raises the fixed-prime local sum
to the Euler-totient power `φ(p ^ r)`.

The resulting element remains in Bernstein's fixed-prime ideal and is
pointwise congruent to `1` modulo `p ^ r`.
-/

universe u

namespace CFSG.BrauerInduction.Bernstein

variable {k G : Type u} [Field k] [Group G]
variable (p r : ℕ) [Fact p.Prime]

/--
The Euler-totient power of Bernstein's fixed-prime local sum.
-/
@[expose] noncomputable def localSumPower
    [Finite G] [CharZero k] [IsAlgClosed k] :
    ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G) :=
  PElementary.localSumElement p ^ (p ^ r).totient

@[simp]
lemma coe_localSumPower
    [Finite G] [CharZero k] [IsAlgClosed k] :
    (localSumPower (k := k) (G := G) p r : ClassFun k G) =
        PElementary.localSum (k := k) p ^ (p ^ r).totient :=
  rfl

/--
The Euler-totient power of the local sum remains in the fixed-prime
Bernstein ideal.
-/
lemma localSumPower_mem_JIdeal
    [Finite G] [CharZero k] [IsAlgClosed k] :
    localSumPower (k := k) (G := G) p r ∈ JIdeal p := by
  unfold localSumPower
  have hpos : 0 < (p ^ r).totient := by
    apply Nat.totient_pos.mpr
    exact Nat.pos_of_neZero (p ^ r)
  exact
    (JIdeal (k := k) (G := G) p).pow_mem_of_mem
      (localSumElement_mem_JIdeal p)
      (p ^ r).totient hpos

/--
The difference between `localSumPower p r` and `1` has values divisible by
`p ^ r`.
-/
lemma localSumPower_sub_one_apply
    [Finite G] [CharZero k] [IsAlgClosed k]
    (g : G) :
    ∃ m : ℤ,
      ((localSumPower (k := k) (G := G) p r - 1 :
          ClassFun.IntegralCyclotomicCharacterRing) :
        ClassFun k G) g =
          (m : k) ∧ (((p ^ r : ℕ) : ℤ) ∣ m) := by
  refine ClassFun.pow_totient_sub_one_apply_of_not_dvd p r ?_ g
  intro g
  exact localSum_apply_not_dvd p g

/--
Every integer representing a value of `localSumPower p r - 1` is divisible
by `p ^ r`.
-/
lemma localSumPower_sub_one_values_dvd
    [Finite G] [CharZero k] [IsAlgClosed k] :
    ∀ g : G, ∀ m : ℤ,
      ((localSumPower (k := k) (G := G) p r - 1 :
          ClassFun.IntegralCyclotomicCharacterRing) :
        ClassFun k G) g = (m : k) → (((p ^ r : ℕ) : ℤ) ∣ m) := by
  intro g m hm
  change
    (PElementary.localSum (k := k) p ^ (p ^ r).totient - 1) g = (m : k)
    at hm
  exact
    ClassFun.pow_totient_sub_one_values_dvd_of_not_dvd
      p r (localSum_apply_not_dvd p) g m hm

end CFSG.BrauerInduction.Bernstein
