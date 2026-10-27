module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_6_d

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 12.6(e). -/
public theorem CFSG.corollary_12_6_e
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    ∀ x : G, x ∈ subgroupCentralizerIn E₁ A → x ≠ 1 →
      elementCentralizerIn (section10Msigma M) x = ⊥ := by
  classical
  intro x hxC hxne
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, ⟨hE12E, hHallE12⟩, ⟨hE1E12, hHallE1⟩, hE2, hE3⟩
  let C : Subgroup G := subgroupCentralizerIn E₁ A
  obtain ⟨q, z, hz_zpowx, _hzC, _hzne, hX_C⟩ :=
    section12_exists_primeOrder_zpowers_in_pre (B := C) (by simpa [C] using hxC) hxne
  let X : Subgroup G := Subgroup.zpowers z
  have hX_C' : X ∈ section10PrimeOrderSubgroupsIn q C := by
    simpa [X] using hX_C
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX_C') with
    ⟨hX_le_C, hXcard⟩
  have hC_le_E1 : C ≤ E₁ := by
    intro y hy
    exact hy.1
  have hX_le_E1 : X ≤ E₁ := hX_le_C.trans hC_le_E1
  have hXM : X ≤ M := hX_le_E1.trans (hE1E12.trans (hE12E.trans hcomp.2.1))
  have hqτ1 : q ∈ section12Tau1Primes M := by
    have hqX : q.val ∣ Nat.card X := by rw [hXcard]
    have hqE1 : q.val ∣ Nat.card E₁ :=
      hqX.trans (Subgroup.card_dvd_of_le hX_le_E1)
    exact hHallE1.p_in_pi_of_p_dvd_card q
      (by simpa [natCard_subgroupOf_eq _ _ hE1E12] using hqE1)
  have hA_normX : A ≤ Subgroup.normalizer (X : Set G) :=
    section12_rankTwo_le_normalizer_of_le_centralizerIn_pre (E₁ := E₁) (A := A) hX_le_C
  have hCX : subgroupCentralizerIn (section10Msigma M) X = ⊥ :=
    section12_subgroupCentralizerIn_primeOrder_eq_bot_of_tau13_pre
      hM hEdata hp hA hXM hXcard (Or.inl hqτ1) hA_normX
  exact le_bot_iff.mp (by
    rw [← hCX]
    exact section12_elementCentralizerIn_le_subgroupCentralizerIn_zpowers_of_mem_zpowers_pre
      (H := section10Msigma M) hz_zpowx)


end Section12
