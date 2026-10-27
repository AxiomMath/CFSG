module

public import CFSG.ThirdParty.BrauerInduction.Background.Arithmetic.PrimePowerCongruence
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Integral

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Prime-power congruences for integer-valued class functions

This file lifts the elementary integer congruence modulo `p ^ r` pointwise to
class functions whose integer values are all prime to `p`.
-/

universe u v

namespace CFSG.ClassFun

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
If every value of `f` is represented by an integer not divisible by `p`, then
every value of `f ^ φ(p ^ r) - 1` is represented by an integer divisible by
`p ^ r`.
-/
lemma pow_totient_sub_one_apply_of_not_dvd
    (p r : ℕ) [Fact p.Prime]
    {f : ClassFun k G}
    (hf :
      ∀ g : G,
        ∃ m : ℤ,
          f g = (m : k) ∧
          ¬ (p : ℤ) ∣ m)
    (g : G) :
    ∃ m : ℤ,
      (f ^ (p ^ r).totient - 1) g = (m : k) ∧
      (((p ^ r : ℕ) : ℤ) ∣ m) := by
  obtain ⟨a, ha, ha_not_dvd⟩ := hf g
  refine ⟨a ^ (p ^ r).totient - 1, ?_, ?_⟩
  · simp [ha]
  · exact
      Int.modEq_iff_dvd.mp
        (Int.pow_totient_primePow_modEq_one
          p r ha_not_dvd).symm

/--
Under the same hypotheses, `f ^ φ(p ^ r) - 1` is integer-valued.
-/
lemma pow_totient_sub_one_mem_C_Z_of_not_dvd
    (p r : ℕ) [Fact p.Prime]
    {f : ClassFun k G}
    (hf :
      ∀ g : G,
        ∃ m : ℤ,
          f g = (m : k) ∧
          ¬ (p : ℤ) ∣ m) :
    f ^ (p ^ r).totient - 1 ∈ C_Z k G := by
  intro g
  obtain ⟨m, hm, _⟩ :=
    pow_totient_sub_one_apply_of_not_dvd
      p r hf g
  exact ⟨m, hm⟩

/--
Every integer representing a value of `f ^ φ(p ^ r) - 1` is divisible by
`p ^ r`.
-/
lemma pow_totient_sub_one_values_dvd_of_not_dvd [CharZero k]
    (p r : ℕ) [Fact p.Prime]
    {f : ClassFun k G}
    (hf :
      ∀ g : G,
        ∃ m : ℤ,
          f g = (m : k) ∧
          ¬ (p : ℤ) ∣ m) :
    ∀ g : G, ∀ m : ℤ,
      (f ^ (p ^ r).totient - 1) g = (m : k) →
      (((p ^ r : ℕ) : ℤ) ∣ m) := by
  intro g m hm
  obtain ⟨n, hn, hn_dvd⟩ :=
    pow_totient_sub_one_apply_of_not_dvd
      p r hf g
  have hmn : m = n :=
    Int.cast_injective (hm.symm.trans hn)
  simpa [hmn] using hn_dvd

end CFSG.ClassFun
