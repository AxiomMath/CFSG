module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 8.1: two fixed points with involutions

If two distinct points of the canonical conjugate action have involutions in
their `F`-stabilizers, an involution of `F` interchanges the points and the
first point stabilizer is strongly embedded in `F`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

private theorem isInvolution_subtype_of_mem
    {X : Type u} [Group X] {F : Subgroup X} {x : X}
    (hxF : x ∈ F) (hx : IsInvolution x) :
    IsInvolution (⟨x, hxF⟩ : F) := by
  constructor
  · intro h
    exact hx.ne_one (congrArg Subtype.val h)
  · apply Subtype.ext
    exact hx.sq_eq_one

/-- Involutions fixing distinct points have a product of odd order. -/
private theorem orderOf_mul_odd_of_distinct_fixedPoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {s t : X}
    {delta zeta : conjugateCosetSpace M}
    (hs : IsInvolution s) (ht : IsInvolution t)
    (hsdelta : s • delta = delta) (htzeta : t • zeta = zeta)
    (hne : delta ≠ zeta) :
    Odd (orderOf (s * t)) := by
  rcases QuotientGroup.mk_surjective delta with ⟨g, rfl⟩
  have hsStab : s ∈ MulAction.stabilizer X
      (QuotientGroup.mk g : conjugateCosetSpace M) :=
    MulAction.mem_stabilizer_iff.mpr hsdelta
  have hsConjM : rightConjugateElem s g ∈ M := by
    apply rightConjugateElem_mem_of_mem_rightConjugate (g := g)
    simpa [conjugateCoset_stabilizer] using hsStab
  have htNotStab : t ∉ MulAction.stabilizer X
      (QuotientGroup.mk g : conjugateCosetSpace M) := by
    intro htStab
    exact hne ((hM.involution_fixed_coset_unique ht).unique
      (MulAction.mem_stabilizer_iff.mp htStab) htzeta)
  have htConjNotM : rightConjugateElem t g ∉ M := by
    intro htConjM
    apply htNotStab
    rw [conjugateCoset_stabilizer]
    have hmem := rightConjugateElem_mem_rightConjugate (g := g⁻¹) htConjM
    simpa [rightConjugateElem, mul_assoc] using hmem
  have hoddConj : Odd (orderOf
      (rightConjugateElem s g * rightConjugateElem t g)) :=
    hM.orderOf_mul_odd_of_mem_not_mem hsConjM
      (isInvolution_rightConjugateElem hs) htConjNotM
      (isInvolution_rightConjugateElem ht)
  have hmul :
      rightConjugateElem s g * rightConjugateElem t g =
        rightConjugateElem (s * t) g := by
    simp [rightConjugateElem, mul_assoc]
  have horder : orderOf (rightConjugateElem (s * t) g) = orderOf (s * t) := by
    exact (MulEquiv.orderOf_eq (MulAut.conj g).symm (s * t))
  rw [hmul, horder] at hoddConj
  exact hoddConj

/-- The odd-product conjugator can be chosen inside any subgroup containing
the two involutions. -/
private theorem exists_involution_conjugator_mem
    {X : Type u} [Group X] [Finite X] (F : Subgroup X) {s t : X}
    (hsF : s ∈ F) (htF : t ∈ F)
    (hs : IsInvolution s) (ht : IsInvolution t)
    (hst : s ≠ t) (hodd : Odd (orderOf (s * t))) :
    ∃ r : F, IsInvolution (r : X) ∧ rightConjugateElem s (r : X) = t := by
  let sF : F := ⟨s, hsF⟩
  let tF : F := ⟨t, htF⟩
  have hsFI : IsInvolution sF := isInvolution_subtype_of_mem hsF hs
  have htFI : IsInvolution tF := isInvolution_subtype_of_mem htF ht
  have hstF : sF ≠ tF := by
    intro h
    exact hst (congrArg Subtype.val h)
  have hoddF : Odd (orderOf (sF * tF)) := by
    rw [← Subgroup.orderOf_coe]
    exact hodd
  obtain ⟨r, hr, hconj⟩ :=
    exists_involution_conjugator_of_odd_product hsFI htFI hstF hoddF
  refine ⟨r, ?_, ?_⟩
  · exact ⟨fun h => hr.ne_one (Subtype.ext h), congrArg Subtype.val hr.sq_eq_one⟩
  · exact congrArg Subtype.val hconj

private theorem pointStabilizerIn_eq_stabilizer
    {X Omega : Type*} [Group X] [MulAction X Omega]
    (F : Subgroup X) (omega : Omega) :
    pointStabilizerIn F omega = MulAction.stabilizer F omega := by
  ext f
  change ((f : X) • omega = omega) ↔ (f : X) • omega = omega
  rfl

namespace IsStronglyEmbedded

/-- Lemma 8.1 of the source. -/
public theorem lemma_8_1
    {X : Type u} [Group X] [Finite X] {M F : Subgroup X}
    (hM : IsStronglyEmbedded M)
    {delta zeta : conjugateCosetSpace M}
    (hne : delta ≠ zeta)
    (hdelta : HasStabilizerInvolution F delta)
    (hzeta : HasStabilizerInvolution F zeta) :
    Lemma81Conclusion M F delta zeta := by
  rcases hdelta with ⟨s, hsF, hs, hsdelta⟩
  rcases hzeta with ⟨t, htF, ht, htzeta⟩
  have hst : s ≠ t := by
    intro hst
    apply hne
    exact (hM.involution_fixed_coset_unique hs).unique hsdelta (hst ▸ htzeta)
  have hodd : Odd (orderOf (s * t)) :=
    orderOf_mul_odd_of_distinct_fixedPoints hM hs ht hsdelta htzeta hne
  obtain ⟨r, hr, hconj⟩ :=
    exists_involution_conjugator_mem F hsF htF hs ht hst hodd
  have hrr : (r : X) * (r : X) = 1 := by
    simpa [pow_two] using hr.sq_eq_one
  have htr : t * (r : X) = (r : X) * s := by
    rw [← hconj]
    simp [rightConjugateElem, hr.inv_eq_self, hrr, mul_assoc]
  have hrdelta : (r : X) • delta = zeta := by
    apply (hM.involution_fixed_coset_unique ht).unique
    · calc
        t • ((r : X) • delta) =
            (t * (r : X)) • delta := by rw [smul_smul]
        _ = ((r : X) * s) • delta := by rw [htr]
        _ = (r : X) • (s • delta) := by rw [smul_smul]
        _ = (r : X) • delta := by rw [hsdelta]
    · exact htzeta
  have hrzeta : (r : X) • zeta = delta := by
    calc
      (r : X) • zeta = (r : X) • ((r : X) • delta) := by rw [hrdelta]
      _ = ((r : X) * (r : X)) • delta := by rw [smul_smul]
      _ = delta := by rw [hrr]; simp
  refine ⟨⟨r, hr, hrdelta, hrzeta⟩, ?_⟩
  rw [pointStabilizerIn_eq_stabilizer]
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    have hrfix : (r : X) • delta = delta := by
      have hrmem : r ∈ MulAction.stabilizer F delta := by
        have hrtop : r ∈ (⊤ : Subgroup F) := Subgroup.mem_top r
        exact htop.symm ▸ hrtop
      have hrfixF := MulAction.mem_stabilizer_iff.mp hrmem
      change (r : X) • delta = delta at hrfixF
      exact hrfixF
    exact hne (hrfix.symm.trans hrdelta)
  · refine ⟨⟨s, hsF⟩, ?_, isInvolution_subtype_of_mem hsF hs⟩
    exact MulAction.mem_stabilizer_iff.mpr hsdelta
  · intro g hgH x hxH hxConj hx
    have hxAmbient : IsInvolution (x : X) := by
      exact ⟨fun h => hx.ne_one (Subtype.ext h), congrArg Subtype.val hx.sq_eq_one⟩
    have hxdelta : (x : X) • delta = delta :=
      MulAction.mem_stabilizer_iff.mp hxH
    have hxother : (x : X) • ((g : X)⁻¹ • delta) = (g : X)⁻¹ • delta := by
      have hconjEq :
          rightConjugate (MulAction.stabilizer F delta) g =
            MulAction.stabilizer F (g⁻¹ • delta) :=
        rightConjugate_stabilizer delta g
      have hxStab : x ∈ MulAction.stabilizer F (g⁻¹ • delta) :=
        hconjEq ▸ hxConj
      have hxotherF := MulAction.mem_stabilizer_iff.mp hxStab
      change (x : X) • ((g : X)⁻¹ • delta) = (g : X)⁻¹ • delta at hxotherF
      exact hxotherF
    have hpoint : delta = (g : X)⁻¹ • delta :=
      (hM.involution_fixed_coset_unique hxAmbient).unique hxdelta hxother
    apply hgH
    apply MulAction.mem_stabilizer_iff.mpr
    change (g : X) • delta = delta
    have h := congrArg (fun omega => (g : X) • omega) hpoint
    simpa [smul_smul] using h

end IsStronglyEmbedded
end CFSG.BenderSuzuki
