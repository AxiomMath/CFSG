module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma81

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 8.2: transport away from the base point

`Proposition82aAtBase` is the retained inductive source boundary from the
minimal-counterexample argument.  This module proves the conjugation step that
the source leaves implicit: its conclusion at the distinguished coset implies
the corresponding conclusion at every fixed coset.

Unlike the temporary Proposition 8.4 statement scaffold, the declarations in
this file are proved theorems.  They will feed the proof of Proposition 8.2(b)
and then the actual induction in Proposition 8.4.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- Conjugation of a subgroup transports its fixed points by the ambient group
action. -/
public noncomputable def theorem4bFixedPoints_rightConjugateEquiv
    {X : Type u} [Group X] (M Y : Subgroup X) (g : X) :
    theorem4bFixedPoints M (rightConjugate Y g) ≃
      theorem4bFixedPoints M Y where
  toFun omega := by
    refine ⟨g • (omega : conjugateCosetSpace M), ?_⟩
    intro y hyY
    have hyConj : rightConjugateElem y g ∈ rightConjugate Y g :=
      rightConjugateElem_mem_rightConjugate hyY
    calc
      y • (g • (omega : conjugateCosetSpace M)) =
          g • (rightConjugateElem y g •
            (omega : conjugateCosetSpace M)) := by
        simp [rightConjugateElem, smul_smul, mul_assoc]
      _ = g • (omega : conjugateCosetSpace M) := by
        rw [omega.property _ hyConj]
  invFun omega := by
    refine ⟨g⁻¹ • (omega : conjugateCosetSpace M), ?_⟩
    intro x hx
    rcases hx with ⟨y, hyY, rfl⟩
    change (g⁻¹ * y * (g⁻¹)⁻¹) •
        (g⁻¹ • (omega : conjugateCosetSpace M)) =
      g⁻¹ • (omega : conjugateCosetSpace M)
    calc
      (g⁻¹ * y * (g⁻¹)⁻¹) •
          (g⁻¹ • (omega : conjugateCosetSpace M)) =
        g⁻¹ • (y • (omega : conjugateCosetSpace M)) := by
          simp [smul_smul, mul_assoc]
      _ = g⁻¹ • (omega : conjugateCosetSpace M) := by
        rw [omega.property _ hyY]
  left_inv omega := by
    apply Subtype.ext
    simp [smul_smul]
  right_inv omega := by
    apply Subtype.ext
    simp [smul_smul]

/-- Proposition 8.2(a) at an arbitrary fixed point, proved by moving that
point to the base coset, applying `Proposition82aAtBase`, and conjugating the
result back. -/
public theorem Proposition82aAtBase.exists_involution_centralizing_at_fixedPoint
    {X : Type u} [Group X] [Finite X] {M Y : Subgroup X}
    (h82a : Proposition82aAtBase M)
    {omega : conjugateCosetSpace M}
    (homega : omega ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y)
    (hfixed : 3 ≤ Nat.card (theorem4bFixedPoints M Y)) :
    ∃ u : X,
      u ∈ MulAction.stabilizer X omega ∧
        IsInvolution u ∧ Y ≤ Subgroup.centralizer ({u} : Set X) := by
  rcases QuotientGroup.mk_surjective omega with ⟨g, rfl⟩
  let Yg : Subgroup X := rightConjugate Y g
  have hYStab : Y ≤ MulAction.stabilizer X
      (QuotientGroup.mk g : conjugateCosetSpace M) := by
    intro y hyY
    exact MulAction.mem_stabilizer_iff.mpr (homega y hyY)
  have hYStab' : Y ≤ rightConjugate M g⁻¹ := by
    simpa [conjugateCoset_stabilizer] using hYStab
  have hYgM : Yg ≤ M := by
    intro x hx
    dsimp [Yg] at hx
    rcases hx with ⟨y, hyY, rfl⟩
    simpa [rightConjugateElem] using
      (rightConjugateElem_mem_of_mem_rightConjugate (hYStab' hyY))
  have hcardEq :
      Nat.card (theorem4bFixedPoints M Yg) =
        Nat.card (theorem4bFixedPoints M Y) :=
    Nat.card_congr (theorem4bFixedPoints_rightConjugateEquiv M Y g)
  have hfixedYg : 3 ≤ Nat.card (theorem4bFixedPoints M Yg) := by
    rw [hcardEq]
    exact hfixed
  obtain ⟨u, huM, hu, hcentral⟩ :=
    h82a.exists_involution_centralizing hYgM hfixedYg
  let ug : X := rightConjugateElem u g⁻¹
  refine ⟨ug, ?_, isInvolution_rightConjugateElem hu, ?_⟩
  · rw [conjugateCoset_stabilizer]
    exact rightConjugateElem_mem_rightConjugate huM
  · intro y hyY
    have hyConj : rightConjugateElem y g ∈ Yg :=
      rightConjugateElem_mem_rightConjugate hyY
    have hcomm : rightConjugateElem y g * u =
        u * rightConjugateElem y g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcentral hyConj)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm' := congrArg (fun z : X => g * z * g⁻¹) hcomm
    simpa [ug, rightConjugateElem, mul_assoc] using hcomm'

/-- The transported base-point theorem supplies the source-facing conclusion
of Proposition 8.2(a) for any fixed subgroup `Y`. -/
public theorem Proposition82aAtBase.proposition82aConclusion
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h82a : Proposition82aAtBase M) (Y : Subgroup X) :
    Proposition82aConclusion M Y := by
  intro omega homega hfixed
  exact h82a.exists_involution_centralizing_at_fixedPoint homega hfixed

private theorem proposition82_isInvolution_subtype_of_mem
    {X : Type u} [Group X] {H : Subgroup X} {x : X}
    (hxH : x ∈ H) (hx : IsInvolution x) :
    IsInvolution (⟨x, hxH⟩ : H) := by
  constructor
  · intro h
    exact hx.ne_one (congrArg Subtype.val h)
  · apply Subtype.ext
    exact hx.sq_eq_one

/-- An ambient involution in `H` lies in the embedded involution core of
`H`. -/
private theorem involution_mem_involutionCoreIn
    {X : Type u} [Group X] {H : Subgroup X} {x : X}
    (hxH : x ∈ H) (hx : IsInvolution x) :
    x ∈ involutionCoreIn H := by
  let xh : H := ⟨x, hxH⟩
  have hxh : IsInvolution xh :=
    proposition82_isInvolution_subtype_of_mem hxH hx
  have hxhCore : xh ∈ involutionCore H := by
    rw [involutionCore_eq_closure]
    exact Subgroup.subset_closure hxh
  exact ⟨xh, hxhCore, rfl⟩

namespace IsStronglyEmbedded

/-- Proposition 8.2(b), derived from its pointwise part (a) and Lemma 8.1. -/
public theorem proposition_8_2_b
    {X : Type u} [Group X] [Finite X] {M Y : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (h82a : Proposition82aConclusion M Y) :
    Proposition82bConclusion M Y := by
  intro F hcore _hFnorm hfixed
  have hstabilizerInvolution : ∀ (omega : conjugateCosetSpace M),
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y →
        HasStabilizerInvolution F omega := by
    intro omega homega
    obtain ⟨u, huStab, hu, hYu⟩ := h82a omega homega hfixed
    have huCentralizer : u ∈ Subgroup.centralizer (Y : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyY
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYu hyY)
    refine ⟨u, hcore (involution_mem_involutionCoreIn huCentralizer hu),
      hu, ?_⟩
    exact MulAction.mem_stabilizer_iff.mp huStab
  constructor
  · intro delta zeta hdelta hzeta
    by_cases hdz : delta = zeta
    · refine ⟨1, ?_⟩
      simp [hdz]
    · obtain ⟨hswap, _⟩ :=
        hM.lemma_8_1 hdz (hstabilizerInvolution delta hdelta)
          (hstabilizerInvolution zeta hzeta)
      exact ⟨hswap.choose, hswap.choose_spec.2.1⟩
  · intro omega homega
    let p : theorem4bFixedPoints M Y := ⟨omega, homega⟩
    have hnontrivial : Nontrivial (theorem4bFixedPoints M Y) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    letI : Nontrivial (theorem4bFixedPoints M Y) := hnontrivial
    obtain ⟨q, hqp⟩ := exists_ne p
    have hqomega : (q : conjugateCosetSpace M) ≠ omega := by
      intro h
      apply hqp
      apply Subtype.ext
      exact h
    exact (hM.lemma_8_1 hqomega.symm
      (hstabilizerInvolution omega homega)
      (hstabilizerInvolution q q.property)).2

end IsStronglyEmbedded

end CFSG.BenderSuzuki
