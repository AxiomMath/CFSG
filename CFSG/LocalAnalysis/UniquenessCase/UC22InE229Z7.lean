module

import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Steps

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem exists_not_mem_commute_of_prime (k : Sec7Core4 G) (h75 : Step75 k) (h72L : Step72L k)
    (h76C : Step76C k) {H : Subgroup G} (hH : Config k H) {x y : G} (hxHM : x ∈ H ⊓ k.M)
    (hyHM : y ∈ H ⊓ k.M) (hxp : IsPGroup k.p (Subgroup.zpowers x)) (hx1 : x ≠ 1)
    (hy : (orderOf y).Prime) (hy2 : orderOf y ≠ 2) (hyp : orderOf y ≠ k.p)
    (hxy : x * y = y * x) : ∃ j : G, j ∉ k.M ∧ j * y = y * j := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  let K : Subgroup G := (CFSG.pPrimeCore k.p ↥H).map H.subtype
  let J : Subgroup G := layerLift k.p H
  have hKcop : Nat.Coprime k.p (Nat.card K) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hcentJK : J ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := J) (H₂ := K)).mp (h75 H hH)
  by_cases hyK : y ∈ K
  · obtain ⟨j, hjJ, hjM⟩ := SetLike.not_le_iff_exists.mp (h72L H hH)
    exact ⟨j, hjM, (Subgroup.mem_centralizer_iff.mp (hcentJK hjJ) y hyK).symm⟩
  have hxK : x ∉ K := by
    intro hxK
    obtain ⟨e, he⟩ := hxp.exists_card_eq
    refine hx1 (CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hxK
      (Nat.Coprime.pow_left e hKcop).symm ?_)
    rw [← he, Nat.card_zpowers]
    exact pow_orderOf_eq_one x
  obtain ⟨j, hjJ, hjP, hjM, hjcomm⟩ := h76C H hH x y hxHM hyHM hxp hxK hy hy2 hyp hyK hxy
  let c' : G := ⁅j, y⁆
  have hcK : c' ∈ K := by
    rw [show c' = j * y * j⁻¹ * y⁻¹ by simp [c', commutatorElement_def]]
    exact hjcomm
  have hcj : Commute c' j := Subgroup.mem_centralizer_iff.mp (hcentJK hjJ) c' hcK
  obtain ⟨e, he⟩ := hjP.exists_card_eq
  have hjpow : j ^ k.p ^ e = 1 := by
    rw [← he, Nat.card_zpowers]
    exact pow_orderOf_eq_one j
  have hcpow : c' ^ (k.p ^ e) = 1 := by
    have h := CFSG.commutator_pow_eq_one_of_pow_eq_one_of_commute
      (x := j) (g := y) (p := k.p ^ e) (by simpa [c'] using hcj) hjpow
    simpa [c'] using h
  have hc1 : c' = 1 := CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hcK
    (Nat.Coprime.pow_left e hKcop).symm hcpow
  have hpc : j * y * j⁻¹ * y⁻¹ = 1 := by simpa [c', commutatorElement_def] using hc1
  refine ⟨j, hjM, ?_⟩
  calc j * y = (j * y * j⁻¹ * y⁻¹) * (y * j) := by group
    _ = y * j := by rw [hpc, one_mul]

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
