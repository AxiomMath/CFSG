module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.QdNotInvolvedOfAbelianSylowTwo

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem D subnode: `Qd(p)` excluded by the two-prime structure

This module proves the exact source step of the proof of Theorem D
(`refs/glauberman-p-stable.tex` L1979–L1981): if `p` is odd, the only prime
divisors of `|G|` are `p` and a prime `q ≠ p`, and the Sylow `q`-subgroups are
Abelian, then every Sylow `2`-subgroup is Abelian and therefore `Qd(p)` is not
involved in `G`.

The Sylow `2` argument is a case split:

* if `2 ∣ |G|`, the two-prime hypothesis forces `q = 2`, and Abelianness comes
  from the given Sylow `q`-subgroup hypothesis;
* if `2 ∤ |G|`, every Sylow `2`-subgroup has order one, hence is trivial and
  Abelian.

The conclusion is then `Glauberman.qd_not_involved_of_abelian_sylow_two`.
-/

namespace CFSG.Glauberman

universe u

/-- If `p` is odd, `q ≠ p` is prime, every Sylow `q`-subgroup of `G` is Abelian,
and `p` and `q` are the only prime divisors of `|G|`, then `Qd(p)` is not involved
in `G`. -/
public theorem qd_not_involved_of_two_prime_divisors
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type u} [Group G] [Finite G]
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hSylowQ : ∀ T : Sylow q G, IsMulCommutative (T : Subgroup G))
    (hdiv : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p ∨ r = q) :
    ¬ Involved (Qd p) G := by
  classical
  have hSylow2 : ∀ T : Sylow 2 G, IsMulCommutative (T : Subgroup G) := by
    intro T
    by_cases h2 : 2 ∣ Nat.card G
    · have h2pq : 2 = p ∨ 2 = q := hdiv 2 Nat.prime_two h2
      have h2q : q = 2 := by
        rcases h2pq with h2p | h2q
        · exact False.elim (hpodd h2p.symm)
        · exact h2q.symm
      subst q
      exact hSylowQ T
    · have hTcard : Nat.card (T : Subgroup G) = 1 := by
        rw [Sylow.card_eq_multiplicity T,
          Nat.factorization_eq_zero_of_not_dvd h2, pow_zero]
      have hTbot : (T : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp hTcard
      rw [hTbot]
      infer_instance
  exact qd_not_involved_of_abelian_sylow_two (p := p) hpodd (G := G) hSylow2

end CFSG.Glauberman
