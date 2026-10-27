module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_g
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_2_a
public import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Finished results from BG Section 12

This file contains the proved prefix of Section 12 of
`Local Analysis for the Odd Order Theorem`.
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section12_eq_conjBy_inv_of_conjBy_eq_pre
    {H K : Subgroup G} {g : G} (h : H.conjBy g = K) :
    H = K.conjBy g⁻¹ := by
  calc
    H = (H.conjBy g).conjBy g⁻¹ := by
      rw [section8_conjBy_conjBy]
      simpa using (section8_conjBy_one H).symm
    _ = K.conjBy g⁻¹ := by rw [h]

omit [IsMinCE G] in
public theorem CFSG.section12_mem_conjugates_self_pre
    {M X : Subgroup G} (hXM : X ≤ M) :
    M ∈ section10ConjugatesContaining M X := by
  exact ⟨1, (section8_conjBy_one M).symm, hXM⟩

omit [IsMinCE G] in
public theorem CFSG.section12_mem_conjugates_of_conjBy_eq_pre
    {M N X : Subgroup G} {g : G} (hconj : N.conjBy g = M) (hXN : X ≤ N) :
    N ∈ section10ConjugatesContaining M X := by
  exact ⟨g⁻¹, section12_eq_conjBy_inv_of_conjBy_eq_pre hconj, hXN⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_mem_conjugates_forward_of_conjBy_eq_pre
    {M N X : Subgroup G} {g : G} (hconj : M.conjBy g = N) (hXN : X ≤ N) :
    N ∈ section10ConjugatesContaining M X := by
  exact ⟨g, hconj.symm, hXN⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_eq_of_conjugation_transitive_and_centralizer_le_pre
    {Ω : Set (Subgroup G)} {Q₁ Q₂ X : Subgroup G}
    (htrans : ConjugationActionTransitiveOn (Subgroup.centralizer (X : Set G)) Ω)
    (hQ₁ : Q₁ ∈ Ω) (hQ₂ : Q₂ ∈ Ω)
    (hC_le_Q₁ : Subgroup.centralizer (X : Set G) ≤ Q₁) :
    Q₂ = Q₁ := by
  rcases htrans Q₁ hQ₁ Q₂ hQ₂ with ⟨c, hc⟩
  have hcQ₁ : (c : G) ∈ Q₁ := hC_le_Q₁ c.property
  have hfix : Q₁.conjBy (c : G) = Q₁ := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.conjBy, Subgroup.mem_map] at hx
      rcases hx with ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hcQ₁) y).1 hy
    · intro hx
      rw [Subgroup.conjBy, Subgroup.mem_map]
      have hc_inv_norm : (c : G)⁻¹ ∈ Subgroup.normalizer (Q₁ : Set G) :=
        (Subgroup.normalizer (Q₁ : Set G)).inv_mem (Subgroup.le_normalizer hcQ₁)
      refine ⟨(c : G)⁻¹ * x * (c : G), ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp hc_inv_norm x).1 hx
      · simp [mul_assoc]
  exact hc.trans hfix

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_tau13_not_sigma
    {M : Subgroup G} {p : Nat.Primes}
    (hp : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M) :
    p ∉ section10SigmaPrimes M := by
  rcases hp with hpτ1 | hpτ3
  · rcases (by simpa [section12Tau1Primes] using hpτ1) with ⟨hpσ, _hpD, _hrank⟩
    exact hpσ
  · rcases (by simpa [section12Tau3Primes] using hpτ3) with ⟨hpσ, _hpD, _hrank⟩
    exact hpσ

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_tau13_primeRank_eq_one
    {M : Subgroup G} {p : Nat.Primes}
    (hp : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M) :
    primeRank p.val M = 1 := by
  rcases hp with hpτ1 | hpτ3
  · rcases (by simpa [section12Tau1Primes] using hpτ1) with ⟨_hpσ, _hpD, hrank⟩
    exact hrank
  · rcases (by simpa [section12Tau3Primes] using hpτ3) with ⟨_hpσ, _hpD, hrank⟩
    exact hrank

omit [IsMinCE G] in
public theorem CFSG.section12_primeRank_conjBy_eq_pre
    (H : Subgroup G) (q : ℕ) (g : G) :
    primeRank q (H.conjBy g) = primeRank q H := by
  let e : H ≃* H.conjBy g :=
    Subgroup.equivMapOfInjective
      (f := (MulAut.conj g).toMonoidHom) H
      (EquivLike.injective (MulAut.conj g))
  exact le_antisymm
    (section12_primeRank_le_of_equiv (R := H) (S := H.conjBy g) q e)
    (section12_primeRank_le_of_equiv (R := H.conjBy g) (S := H) q e.symm)

/-- Lemma 12.2(b). -/
public theorem CFSG.lemma_12_2_b
    {M Mstar X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpX : IsPGroup p.val X) (hXne : X ≠ ⊥) (hXM : X ≤ M)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hhyp :
      (p ∈ section10SigmaPrimes M ∧ M ≠ Mstar) ∨
        p ∈ section12Tau1Primes M ∪ section12Tau3Primes M) :
    section12NotConjugate Mstar M := by
  classical
  intro g hconj
  have hX_Mstar : X ≤ Mstar := Subgroup.le_normalizer.trans hMstar.2
  have hC_le_Mstar : Subgroup.centralizer (X : Set G) ≤ Mstar :=
    (centralizer_le_normalizer X).trans hMstar.2
  rcases hhyp with ⟨hpσM, hM_ne_Mstar⟩ | hpτ13
  · have htrans :
        ConjugationActionTransitiveOn (Subgroup.centralizer (X : Set G))
          (section10ConjugatesContaining M X) :=
      theorem_10_1_b (G := G) hM hpσM hXne hpX hXM
    have hMstar_mem : Mstar ∈ section10ConjugatesContaining M X :=
      section12_mem_conjugates_of_conjBy_eq_pre hconj hX_Mstar
    have hM_mem : M ∈ section10ConjugatesContaining M X :=
      section12_mem_conjugates_self_pre hXM
    have hM_eq_Mstar : M = Mstar :=
      section12_eq_of_conjugation_transitive_and_centralizer_le_pre
        htrans hMstar_mem hM_mem hC_le_Mstar
    exact hM_ne_Mstar hM_eq_Mstar
  · have hpσ_or_tau2 :=
      lemma_12_2_a (G := G) hM hpX hXne hXM hMstar
    rcases hpσ_or_tau2 with hpσstar | hpτ2star
    · have htrans :
          ConjugationActionTransitiveOn (Subgroup.centralizer (X : Set G))
            (section10ConjugatesContaining Mstar X) :=
        theorem_10_1_b (G := G) hMstar.1 hpσstar hXne hpX hX_Mstar
      have hMstar_mem : Mstar ∈ section10ConjugatesContaining Mstar X :=
        section12_mem_conjugates_self_pre hX_Mstar
      have hM_mem : M ∈ section10ConjugatesContaining Mstar X :=
        section12_mem_conjugates_forward_of_conjBy_eq_pre hconj hXM
      have hM_eq_Mstar : M = Mstar :=
        section12_eq_of_conjugation_transitive_and_centralizer_le_pre
          htrans hMstar_mem hM_mem hC_le_Mstar
      have hpσM : p ∈ section10SigmaPrimes M := by
        simpa [hM_eq_Mstar] using hpσstar
      exact (section12_tau13_not_sigma hpτ13) hpσM
    · rcases (by simpa [section12Tau2Primes] using hpτ2star) with ⟨_hpσstar, hrankstar⟩
      have hrankM : primeRank p.val M = 1 :=
        section12_tau13_primeRank_eq_one hpτ13
      have hrank_conj : primeRank p.val M = primeRank p.val Mstar := by
        have h := section12_primeRank_conjBy_eq_pre (H := Mstar) p.val g
        rw [hconj] at h
        exact h
      omega


end Section12
