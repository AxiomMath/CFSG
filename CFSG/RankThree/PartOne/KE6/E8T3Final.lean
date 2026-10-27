module

public import CFSG.RankThree.PartOne.KE6.E8T3Main

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE (D4TrialityLayer OddEndpoint cycloVal planeLocalCoreOdd_of_odd_kernels_abstract
  oddEndpoint_E8_of_native ordinary_E_outer_derived_subgroup_odd localCoreTrivialOn_noninner_E)

theorem planeLocalCoreOdd_E8_three_six
    (hD4 : D4TrialityLayer Tag.E8) (hE6 : E6Layer Tag.E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) :
    PlaneLocalCoreOdd p (adjointGroup .E8 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hout := (ordinary_E_outer_derived_subgroup_odd .E8 (Or.inr (Or.inr rfl)) K).1
  have hcore := localCoreTrivialOn_noninner_E .E8 (Or.inr (Or.inr rfl)) K hp hp3
  have hcm := canonicalRep_mem_monomialSubgroup L (e8T3We ε)
  have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L (e8T3We ε), hcm⟩ =
      e8T3We ε :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have h := e8T3_main hD4 hE6 hε K hf hK hp hp3 hpf L _ hcm hπ
  exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore h.2

theorem oddEndpoint_E8_phi3Phi6
    (hD4 : D4TrialityLayer Tag.E8) (hE6 : E6Layer Tag.E8) :
    OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f ∨ (p : ℤ) ∣ cycloVal 6 ℓ f := by
  refine oddEndpoint_E8_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  rcases hc with hc | hc
  · refine planeLocalCoreOdd_E8_three_six hD4 hE6 (ε := 1) (Or.inl rfl) K hℓ hf hK hp hp3 ?_
    simpa [cycloVal, exhaustionPhi, hK] using hc
  · refine planeLocalCoreOdd_E8_three_six hD4 hE6 (ε := -1) (Or.inr rfl) K hℓ hf hK hp hp3 ?_
    simpa [cycloVal, exhaustionPhi, hK, sub_eq_add_neg] using hc

end CFSG.RankThree.PartOne.KE6
