module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_6_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 12.6(d). -/
public theorem CFSG.corollary_12_6_d
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    ∀ x : G, x ∈ E₃ → x ≠ 1 → elementCentralizerIn (section10Msigma M) x = ⊥ := by
  classical
  intro x hxE3 hxne
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE12, hE1, hE2, ⟨hE3E, hHallE3⟩⟩
  obtain ⟨q, z, hz_zpowx, _hzE3, _hzne, hX_E3⟩ :=
    section12_exists_primeOrder_zpowers_in_pre (B := E₃) hxE3 hxne
  let X : Subgroup G := Subgroup.zpowers z
  have hX_E3' : X ∈ section10PrimeOrderSubgroupsIn q E₃ := by
    simpa [X] using hX_E3
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX_E3') with
    ⟨hX_le_E3, hXcard⟩
  have hXM : X ≤ M := hX_le_E3.trans (hE3E.trans hcomp.2.1)
  have hqτ3 : q ∈ section12Tau3Primes M := by
    have hqX : q.val ∣ Nat.card X := by rw [hXcard]
    have hqE3 : q.val ∣ Nat.card E₃ :=
      hqX.trans (Subgroup.card_dvd_of_le hX_le_E3)
    exact hHallE3.p_in_pi_of_p_dvd_card q
      (by simpa [natCard_subgroupOf_eq _ _ hE3E] using hqE3)
  have hA_normX : A ≤ Subgroup.normalizer (X : Set G) :=
    section12_rankTwo_le_normalizer_of_le_E3_pre hM hEdata hA hX_le_E3
  have hCX : subgroupCentralizerIn (section10Msigma M) X = ⊥ :=
    section12_subgroupCentralizerIn_primeOrder_eq_bot_of_tau13_pre
      hM hEdata hp hA hXM hXcard (Or.inr hqτ3) hA_normX
  exact le_bot_iff.mp (by
    rw [← hCX]
    exact section12_elementCentralizerIn_le_subgroupCentralizerIn_zpowers_of_mem_zpowers_pre
      (H := section10Msigma M) hz_zpowx)


end Section12
