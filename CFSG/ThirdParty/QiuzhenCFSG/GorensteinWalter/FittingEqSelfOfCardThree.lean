module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An odd finite group whose Fitting subgroup has order three is itself its
Fitting subgroup.  The quotient acts faithfully on the cyclic group of order
three, while its automorphism group has order two. -/
public theorem fittingSubgroupOf_eq_self_of_card_three
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G)
    (hUodd : Nat.Coprime 2 (Nat.card U))
    (hFcard : Nat.card (fittingSubgroupOf U) = 3) :
    fittingSubgroupOf U = U := by
  classical
  let F : Subgroup G := fittingSubgroupOf U
  have hUle : U ≤ Subgroup.normalizer (F : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (fittingSubgroupOf_isNormalIn U).2 u hu x hx
    · intro hx
      have hu' : u⁻¹ ∈ U := U.inv_mem hu
      have h := (fittingSubgroupOf_isNormalIn U).2 u⁻¹ hu'
        (u * x * u⁻¹) hx
      simpa [mul_assoc] using h
  let ι : U →* ↥(Subgroup.normalizer (F : Set G)) :=
    { toFun := fun u => ⟨(u : G), hUle u.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  let ρ : U →* MulAut F :=
    (F.normalizerMonoidHom).comp ι
  have hUodd' : Odd (Nat.card U) := Nat.coprime_two_left.mp hUodd
  have hsolv : IsSolvable U := odd_order_theorem U hUodd'
  have hFcyc : IsCyclic F := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card (by simpa [F] using hFcard)
  have hAutcard : Nat.card (MulAut F) = 2 := by
    rw [IsCyclic.card_mulAut F, hFcard, Nat.totient_prime Nat.prime_three]
  have hcentral : U ≤ Subgroup.centralizer (F : Set G) := by
    intro u hu
    let uU : U := ⟨u, hu⟩
    have hρdvdU : orderOf (ρ uU) ∣ Nat.card U := by
      refine (orderOf_map_dvd ρ uU).trans ?_
      simpa using (Subgroup.orderOf_dvd_natCard U uU.2)
    have hρdvd2 : orderOf (ρ uU) ∣ 2 := by
      rw [← hAutcard]
      exact orderOf_dvd_natCard (ρ uU)
    have hcop : Nat.Coprime (orderOf (ρ uU)) 2 := by
      exact (Nat.Coprime.of_dvd_right hρdvdU hUodd).symm
    have hρone : orderOf (ρ uU) = 1 := hcop.eq_one_of_dvd hρdvd2
    have hρeq : ρ uU = 1 := orderOf_eq_one_iff.mp hρone
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hfix : ρ uU ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hρeq]; simp
    have hfix' := congrArg (fun z : F => (z : G)) hfix
    have hconj : (u : G) * (x : G) * (u : G)⁻¹ = (x : G) := by
      simpa [ρ, ι, F, Subgroup.normalizerMonoidHom_apply_apply_coe] using hfix'
    have hcomm : (x : G) * (u : G) = (u : G) * (x : G) := by
      calc
        (x : G) * (u : G) = ((u : G) * (x : G) * (u : G)⁻¹) * (u : G) := by
          rw [hconj]
        _ = (u : G) * (x : G) := by group
    exact hcomm
  have hcentSub : U.subgroupOf U ≤
      Subgroup.centralizer (fittingSubgroup U : Set U) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hcentral (Subgroup.mem_subgroupOf.mp hu)
    have h' := (Subgroup.mem_centralizer_iff.mp h) (x : G)
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subtype.ext h'
  have hcent_le : Subgroup.centralizer (fittingSubgroup U : Set U) ≤
      fittingSubgroup U :=
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  apply le_antisymm
  · exact fittingSubgroupOf_le U
  · intro u hu
    have huSub : (⟨u, hu⟩ : U) ∈ fittingSubgroup U :=
      hcent_le (hcentSub (Subgroup.mem_subgroupOf.mpr hu))
    change u ∈ F
    exact Subgroup.mem_map.mpr ⟨⟨u, hu⟩, huSub, rfl⟩

end CFSG.GorensteinWalter
