module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 2(c)
-/

public theorem proposition_2_c
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ s : G, s ∈ Q → IsInvolution s →
      (∀ u : G, IsInvolution u → u ∉ H →
        IsInvolution (rightConjugateElem s u) ∧ rightConjugateElem s u ∉ H) ∧
        (∀ v : G, IsInvolution v → v ∉ H →
          ∃ u : G, IsInvolution u ∧ u ∉ H ∧ rightConjugateElem s u = v) := by
  classical
  intro s hsQ hs
  have hsH : s ∈ H := hA1.Q_le_H hsQ
  constructor
  · intro u hu hu_not_H
    constructor
    · exact isInvolution_rightConjugateElem hs
    · intro hsuH
      obtain ⟨_h, _hinter, hodd⟩ := proposition_1_a H D Q t hA1 u hu_not_H
      have hsu_conjH : rightConjugateElem s u ∈ rightConjugate H u := by
        rw [rightConjugate, rightConjugateElem, Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨s, hsH, by simp⟩
      have hsu_inter : rightConjugateElem s u ∈ rightConjugate H u ⊓ H :=
        ⟨hsu_conjH, hsuH⟩
      exact
        (not_isInvolution_of_mem_odd_subgroup
          (rightConjugate H u ⊓ H) hodd hsu_inter)
          (isInvolution_rightConjugateElem hs)
  · intro v hv hv_not_H
    have hsv : s ≠ v := by
      intro h
      exact hv_not_H (h ▸ hsH)
    have hodd : Odd (orderOf (s * v)) :=
      proposition_2_a H D Q t hA1 s v hsH hs hv hv_not_H
    obtain ⟨u, hu, hconj⟩ :=
      exists_involution_conjugator_of_odd_product hs hv hsv hodd
    have hu_not_H : u ∉ H := by
      intro huH
      apply hv_not_H
      rw [← hconj]
      exact H.mul_mem (H.mul_mem (H.inv_mem huH) hsH) huH
    exact ⟨u, hu, hu_not_H, hconj⟩

end PFchapter1section1
end CFSG.BenderSuzuki
