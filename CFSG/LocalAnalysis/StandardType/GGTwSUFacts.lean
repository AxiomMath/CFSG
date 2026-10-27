module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
import CFSG.LocalAnalysis.StandardType.GGK1ScUni

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem unitary_split_torus_recipe_facts
    {K : Type} [Field K] [Finite K] [CharP K 2] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥ ∧
      GGOutdiagPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) ∧
      GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  have hp3 : ¬ p ∣ 2 ^ n + 1 :=
    not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  refine ⟨center_statedProj_statedSU_eq_bot hK (by omega),
    NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega) hp hp3,
    ggCenterPrime_unitary_gcd hK hn (by omega) hdq hp hp2
      (fun h => hp3 h.2)⟩

theorem ggTwSU_facts_rec
    {K : Type} [Field K] [Finite K] [CharP K 2] {n d r : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hr : 3 ≤ r)
    (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ 2 ^ n - 1) :
    Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥ ∧
      GGOutdiagPrime 3 (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) ∧
      GGCenterPrime 3 (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
  unitary_split_torus_recipe_facts hK hn (by omega) Nat.prime_three (by norm_num) h3

end CFSG.StandardType

end
