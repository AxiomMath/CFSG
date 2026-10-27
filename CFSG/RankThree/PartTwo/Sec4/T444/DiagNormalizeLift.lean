module

public import CFSG.RankThree.PartTwo.Sec4.T444.Lift
public import CFSG.RankThree.GroupTheory.PerfectSubnormalModNormal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Subgroup
open scoped commutatorElement

theorem solvable_inf_pPrimeCore_of_mem_thetaComponents {G : Type} [Group G] [Finite G]
    {S : Subgroup G} (hS : S ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card S) :
    Group.IsSolvable (S ⊓ CFSG.pPrimeCore 3 G : Subgroup G) := by
  rw [inf_pPrimeCore_eq_of_mem_thetaComponents hS h3]
  have h1 : Group.IsSolvable (aschbacherSolvableCore 3 S) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  exact Group.isSolvable_of_surjective
    (f := S.subtype.subgroupMap (aschbacherSolvableCore 3 S))
    (S.subtype.subgroupMap_surjective _)

theorem eq_of_map_starQuot_eq_of_mem_thetaComponents {G : Type} [Group G] [Finite G]
    {S₁ S₂ : Subgroup G} (h₁ : S₁ ∈ thetaComponents 3 G) (h₂ : S₂ ∈ thetaComponents 3 G)
    (h31 : 3 ∣ Nat.card S₁) (h32 : 3 ∣ Nat.card S₂)
    (h : S₁.map (starQuot G) = S₂.map (starQuot G)) : S₁ = S₂ := by
  have hsup : S₁ ⊔ CFSG.pPrimeCore 3 G = S₂ ⊔ CFSG.pPrimeCore 3 G := by
    have e1 := Subgroup.comap_map_eq (starQuot G) S₁
    have e2 := Subgroup.comap_map_eq (starQuot G) S₂
    have hk : (starQuot G).ker = CFSG.pPrimeCore 3 G := QuotientGroup.ker_mk' _
    rw [hk] at e1 e2
    rw [← e1, ← e2, h]
  exact CFSG.RankThree.GroupTheory.eq_of_perfect_isSubnormal_of_sup_eq_of_solvable_inf
    h₁.1 h₂.1 h₁.2.1 h₂.2.1
    (solvable_inf_pPrimeCore_of_mem_thetaComponents h₁ h31)
    (solvable_inf_pPrimeCore_of_mem_thetaComponents h₂ h32) hsup

end CFSG.RankThree.PartTwo.Sec4
