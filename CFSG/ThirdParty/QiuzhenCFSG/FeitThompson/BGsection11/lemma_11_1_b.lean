module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.lemma_11_1_a

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 11.1(b)

This file contains the Section 11 Lemma 11.1(b) statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 11.1(b). -/
public theorem CFSG.lemma_11_1_b
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {g : G}
    (hgM : g ∉ M) (_hAgM : A ≤ M.conjBy g) (hqσ : q ∈ section10SigmaPrimes M)
    (Q1 : Sylow q.val (section10Msigma M))
    (Q2 : Sylow q.val ((section10Msigma M).conjBy g))
    (hAQ1 :
      A ≤ Subgroup.normalizer
        (section10AmbientSylowSubgroup (section10Msigma M) Q1 : Set G))
    (hAQ2 :
      A ≤ Subgroup.normalizer
        (section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2 : Set G))
    {X : Subgroup G} (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    subgroupCentralizerIn (section10AmbientSylowSubgroup (section10Msigma M) Q1) X = ⊥ ∨
      subgroupCentralizerIn
        (section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2) X =
        ⊥ := by
  classical
  let R1 : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) Q1
  let R2 : Subgroup G :=
    section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨hC1_ne_bot, hC2_ne_bot⟩
  have hR1star :
      R1 ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    simpa [R1] using
      section11_ambientSylow_mem_star_of_sigma h11.maximal hqσ Q1 hAQ1
  have hR2star :
      R2 ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    simpa [R2] using
      section11_ambientSylow_mem_star_of_sigma_conjBy h11.maximal hqσ Q2 hAQ2
  let H : Subgroup G := Subgroup.centralizer (X : Set G)
  have hA_le_H : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxA : x ∈ A := hX.1 hx
    exact ((Subgroup.mem_centralizer_iff.mp (h11.A_eq_centralizer_p_elements.subset hxA).1) a ha).symm
  have hHproper : H ≠ ⊤ := by
    exact section11_centralizer_ne_top_of_prime_order hX.2
  have hHR1_ne_bot : H ⊓ R1 ≠ ⊥ := by
    simpa [H, R1, subgroupCentralizerIn, inf_comm, inf_left_comm, inf_assoc] using hC1_ne_bot
  have hHR2_ne_bot : H ⊓ R2 ≠ ⊥ := by
    simpa [H, R2, subgroupCentralizerIn, inf_comm, inf_left_comm, inf_assoc] using hC2_ne_bot
  obtain ⟨k, hk⟩ :=
    lemma_7_1 (G := G) h11.hypothesis7_1
      (h11.q_not_mem_A_primeSet hqσ) hR1star hR2star
      hA_le_H hHproper hHR1_ne_bot hHR2_ne_bot
  exact section11_lemma_7_1_conclusion h11 hgM hqσ Q1 Q2 k (by simpa [R1, R2] using hk.symm)

end Section11
