module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma91
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Proposition93
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma101
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma103
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma104
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma105
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma106Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Proposition111
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Proposition111Contradiction
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.SourceData
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Hering31

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 6: the Sections 9--11 contradiction

The source proves Theorem 6 by assuming that no nilpotent normal complement
exists, choosing a minimal normal supplement, and running the numbered
Sections 9--11 packages.  This module keeps that source boundary explicit and
isolates the resulting minimal-supplement disjointness theorem.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The source inputs used by Sections 9--11 for one outside involution.
The structure contains only earlier numbered results and implication-shaped
earlier-volume callbacks; it contains no Theorem 6 conclusion. -/
public structure Theorem6InvolutionData
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t : X) where
  lemma83 : Lemma83Data M t
  proposition84 : Proposition84Statement M t lemma83.u
  proposition84_modelSupport :
    Proposition84ModelSupportStatement M t lemma83.u
  peterfalviKSet_nontrivial : ∃ x : X,
    x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1
  base_stabilizer_transitive : IsTransitiveOn M
    {omega : conjugateCosetSpace M |
      omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)}
  rank : TwoRankAtLeastTwo (involutionCore M)
  two_transitive : MulAction.IsMultiplyPretransitive X
    (conjugateCosetSpace M) 2

/-- Under the source contradiction hypothesis, every selected minimal normal
supplement is disjoint from the two-point stabilizer.  The proof assembles the
checked Sections 9--11 packages and ends with the independent Proposition
11.1/Lemma 11.2 fitting contradiction. -/
public theorem minimal_normal_supplement_disjoint
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (h84support : Proposition84ModelSupportStatement M t d83.u)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (htrans : IsTransitiveOn M
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)})
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (hfail : ¬ ∃ Q : Subgroup X,
      IsNormalComplementIn M (M ⊓ rightConjugate M t) Q ∧
        Group.IsNilpotent Q) :
    Disjoint W (M ⊓ rightConjugate M t) := by
  classical
  by_contra hdisjoint
  have hEne : W ⊓ (M ⊓ rightConjugate M t) ≠ ⊥ := by
    intro hbot
    apply hdisjoint
    rw [disjoint_iff]
    exact hbot
  have h96 := corollary_9_6 hM ht htM d83 h84 hW hEne hIne
    ii1Lemma43bCyclic
  have h97 := lemma_9_7 hM ht htM d83 h84 hIne htrans hfail
    ii1Lemma43bCyclic
  have h98 := lemma_9_8 hM ht htM d83 hW hIne hrank h96 h97
    ii1Hering31Ambient
  have h93 := proposition_9_3 hM ht htM d83 h84 hW hIne h96 h97 h98
    ii1Lemma43bCyclic ig911iiNilpotentFrobeniusComplementCyclic
  obtain ⟨d⟩ := lemma_10_1 hM ht htM d83 h84 hW hIne h96 h93
    ii1Lemma43aCoprime ii1Lemma43bCyclic
  obtain ⟨d103⟩ := lemma_10_3 d hM ht htM d83 htwo
  have d104 := lemma_10_4 hM ht htM d83 h84 d
    ii1Lemma45NormalComplement
  have d106 := lemma_10_6 hM ht htM d83 h84 d h97 d103 d104
    ii1Lemma42PrimeTransfer
  obtain ⟨h102⟩ := proposition_10_2 hM ht htM d83 hW h96 h97 d d106
    ii1Lemma42PrimeTransfer h93
  have h113 := lemma_11_3 hM ht htM d83 hW hrank h97 d h102
  have h114 := lemma_11_4
    hM ht htM d83 h84 h84support d h102
  have hNnormF := proposition_11_1 hM ht htM d83 h84 ii1Lemma42PrimeTransfer htwo
    d h102 h113 h114
  exact (proposition111_fitting_contradiction
    hM ht htM d83 h84 d h102 hNnormF).elim

/-- The fixed-involution form of Theorem 6.  The source contradiction is
packaged by assuming that no nilpotent normal complement exists, choosing a
minimal normal supplement, and applying the preceding disjointness theorem
followed by Lemma 9.1. -/
public theorem IsStronglyEmbedded.exists_normal_complement_of_involution
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (h84support : Proposition84ModelSupportStatement M t d83.u)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (htrans : IsTransitiveOn M
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)})
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    ∃ Q : Subgroup X,
      IsNormalComplementIn M (M ⊓ rightConjugate M t) Q ∧
        Group.IsNilpotent Q := by
  classical
  by_contra hfail
  obtain ⟨W, hW⟩ :=
    exists_isMinimalNormalSupplement
      (inf_le_left : M ⊓ rightConjugate M t ≤ M)
  have hdisjoint := minimal_normal_supplement_disjoint
      hM ht htM d83 h84 h84support hW hIne htrans hrank htwo hfail
  obtain ⟨hcomp, hnil, _hregular⟩ :=
    lemma_9_1 ht htM d83 hW hdisjoint hIne htrans
  exact hfail ⟨W, hcomp, hnil⟩

/-- It is enough to prove Theorem 6 for outside involutions.  Every outside
right conjugate of a strongly embedded subgroup is represented by an
involution in the same centralizer coset, hence by the same right-conjugate
subgroup. -/
public theorem IsStronglyEmbedded.theorem6Conclusion_of_involution
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hinv : ∀ {t : X}, IsInvolution t → t ∉ M →
      ∃ Q : Subgroup X,
        IsNormalComplementIn M (M ⊓ rightConjugate M t) Q ∧
          Group.IsNilpotent Q) :
    Theorem6Conclusion M := by
  intro g hgM
  obtain ⟨z, hzM, hz⟩ := hM.exists_involution
  obtain ⟨t, ⟨htCoset, ht⟩, _huniq⟩ :=
    hM.existsUnique_involution_in_centralizer_rightCoset hzM hz hgM
  have hcM : t * g⁻¹ ∈ M := hM.centralizer_le hzM hz htCoset
  have htM : t ∉ M := by
    intro htMem
    apply hgM
    have hg : g = (t * g⁻¹)⁻¹ * t := by simp
    rw [hg]
    exact M.mul_mem (M.inv_mem hcM) htMem
  let c : X := t * g⁻¹
  have hc : c ∈ M := by simpa [c] using hcM
  have htg : t = c * g := by simp [c]
  have hcNorm : c⁻¹ ∈ Subgroup.normalizer (M : Set X) :=
    (Subgroup.normalizer (M : Set X)).inv_mem (Subgroup.le_normalizer hc)
  have hMc : M.conjBy c⁻¹ = M :=
    section11_conjBy_eq_of_mem_normalizer hcNorm
  have hconj : rightConjugate M t = rightConjugate M g := by
    calc
      rightConjugate M t = M.conjBy t⁻¹ := rfl
      _ = M.conjBy (g⁻¹ * c⁻¹) := by rw [htg]; simp
      _ = (M.conjBy c⁻¹).conjBy g⁻¹ :=
        Subgroup.conjBy_mul M g⁻¹ c⁻¹
      _ = M.conjBy g⁻¹ := by rw [hMc]
      _ = rightConjugate M g := rfl
  obtain ⟨Q, hQ, hnil⟩ := hinv ht htM
  refine ⟨Q, ?_, hnil⟩
  simpa [hconj] using hQ

/-- The fixed-involution conclusion obtained from the bundled source data. -/
public theorem IsStronglyEmbedded.exists_normal_complement_of_involution_data
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d : Theorem6InvolutionData M t) :
    ∃ Q : Subgroup X,
      IsNormalComplementIn M (M ⊓ rightConjugate M t) Q ∧
        Group.IsNilpotent Q := by
  exact hM.exists_normal_complement_of_involution
      ht htM d.lemma83 d.proposition84 d.proposition84_modelSupport
      d.peterfalviKSet_nontrivial
      d.base_stabilizer_transitive d.rank d.two_transitive

/-- Theorem 6, packaged from the source data for every outside involution. -/
public theorem IsStronglyEmbedded.theorem_6_of_involution_data
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hdata : ∀ (t : X), IsInvolution t → t ∉ M →
      Nonempty (Theorem6InvolutionData M t)) :
    Theorem6Conclusion M := by
  apply hM.theorem6Conclusion_of_involution
  intro t ht htM
  obtain ⟨d⟩ := hdata t ht htM
  exact hM.exists_normal_complement_of_involution_data ht htM d

end CFSG.BenderSuzuki
