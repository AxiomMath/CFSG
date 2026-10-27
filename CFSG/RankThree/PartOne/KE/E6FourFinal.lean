module

public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.PlaneToral

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open scoped Matrix MatrixGroups

theorem planeLocalCoreOdd_E6_four (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 4).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup .E6 K) := by
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
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by simpa [exhaustionPhi] using hpf
  have hcm := canonicalRep_mem_monomialSubgroup L e6F4U
  have hπ : weylQuotientHom .E6 L ⟨canonicalRep (coxeterSystem .E6) L e6F4U, hcm⟩ = e6F4U :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e6F4U)
  have hnW : ∀ u, weylQuotientHom .E6 L ⟨canonicalRep (coxeterSystem .E6) L e6F4U, hcm⟩ • u =
      (weylMatrix e6F4U) *ᵥ u := fun u => by
    rw [hπ, weylMatrix_mulVec]
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 center_adjointGroup_eq_bot
    (e6_four_solvable K hf hK hp hp3 hpq L _ hcm hnW) hout hcore
    (e6_four_hI K hf hK hp hp3 hpq L _ hcm hnW)

theorem oddEndpoint_E6_phi4 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 4 ℓ f := by
  refine oddEndpoint_E6_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_E6_four K hℓ hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end CFSG.RankThree.PartOne.KE
