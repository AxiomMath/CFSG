module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The dihedral Sylow parameter in odd `PGL₂`

The order of odd `PGL₂(K)` is divisible by eight.  Consequently a Sylow
`2`-subgroup modeled as `D_(2^(m+1))` has `m ≥ 2`, which is the range in
which its central rotation is the unique nontrivial central involution.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- A dihedral model for a Sylow `2`-subgroup of odd `PGL₂(K)` has
parameter at least two. -/
public theorem pgl2_dihedral_sylow_parameter_ge_two
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (P : Sylow 2 (PGL2 K)) {m : ℕ}
    (e : P ≃* DihedralGroup (2 ^ m)) :
    2 ≤ m := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
    rw [hKcard]
    exact hpOdd.pow
  have h8G : 8 ∣ Nat.card (PGL2 K) := by
    rw [pgl2_card_formula K]
    exact dvd_mul_of_dvd_right
      (Nat.eight_dvd_sq_sub_one_of_odd hqOdd) (Nat.card K)
  have hpowG : 2 ^ 3 ∣ Nat.card (PGL2 K) := by
    norm_num
    exact h8G
  have hpowP : 2 ^ 3 ∣ Nat.card P :=
    P.pow_dvd_card_of_pow_dvd_card hpowG
  have hcardP : Nat.card P = 2 * 2 ^ m :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  rw [hcardP] at hpowP
  by_contra hm
  have hmle : m ≤ 1 := by omega
  interval_cases m <;> norm_num at hpowP

end CFSG.GorensteinWalter
