module

public import CFSG.RankThree.PartOne.KE6.EqpPlane
public import CFSG.RankThree.PartOne.KE.PlaneToral

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE (OddEndpoint cycloVal planeLocalCoreOdd_of_toral_kernels_abstract
  oddEndpoint_E6_of_native ordinary_E_outer_derived_subgroup_odd localCoreTrivialOn_noninner_E)
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem planeLocalCoreOdd_E6_evenQPlus (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ = 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 2).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup Tag.E6 K) := by
  classical
  subst hℓ2
  have : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hout := (ordinary_E_outer_derived_subgroup_odd .E6 (Or.inl rfl) K).1
  have hcore := localCoreTrivialOn_noninner_E .E6 (Or.inl rfl) K hp hp3
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) + 1 := by
    simpa [exhaustionPhi] using hpf
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by omega
    subst hf1
    rw [hK] at hpq
    have h3 : (p : ℤ) ∣ 3 := by
      norm_num at hpq
      exact hpq
    have := Int.le_of_dvd (by norm_num) h3
    omega
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 center_adjointGroup_eq_bot
    (e6_qplus_toral K hf2 hK hp hp3 hpq L) hout hcore
    (fun B hB A _ hA hcard hAin => by
      rw [e6_qplus_I_trivial K hf2 hK hp hp3 hpq L hB A hA hcard hAin, Subgroup.card_bot]
      exact odd_one)

theorem oddEndpoint_E6_evenQPlus :
    OddEndpoint .E6 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 2 ℓ f := by
  refine oddEndpoint_E6_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_E6_evenQPlus K hℓ hc.1 hf hK hp hp3 (by simpa [cycloVal, hK] using hc.2)

end CFSG.RankThree.PartOne.KE6
