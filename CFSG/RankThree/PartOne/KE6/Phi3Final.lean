module

public import CFSG.RankThree.PartOne.KE6.Phi3Plane
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

theorem planeLocalCoreOdd_E6_three (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 3).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup Tag.E6 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hout := (ordinary_E_outer_derived_subgroup_odd .E6 (Or.inl rfl) K).1
  have hcore := localCoreTrivialOn_noninner_E .E6 (Or.inl rfl) K hp hp3
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 := by
    simpa [exhaustionPhi] using hpf
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 center_adjointGroup_eq_bot
    (e6_three_toral K hf hK hp hp3 hpq L) hout hcore
    (fun B hB A _ hA hcard hAin => by
      rw [e6_three_I_trivial K hf hK hp hp3 hpq L hB A hA hcard hAin, Subgroup.card_bot]
      exact odd_one)

theorem oddEndpoint_E6_phi3 :
    OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f := by
  refine oddEndpoint_E6_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_E6_three K hℓ hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end CFSG.RankThree.PartOne.KE6
