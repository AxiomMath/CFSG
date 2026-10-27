module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.ConjugateAction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem6
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3

namespace CFSG
end CFSG
open CFSG

/-!
# From a strong-embedding complement to Suzuki's hypotheses

This file isolates the checked interface between the normal-complement output
of Theorem 6 and Peterfalvi's `HypothesisA`.  The difficult existence of the
complement remains separate; once its data are supplied, the coset-action and
parity fields are discharged here.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

namespace IsStronglyEmbedded

/-- A normal complement to a distinct-conjugate intersection has even order:
the strongly embedded subgroup is even, while the complemented intersection
is odd. -/
public theorem normal_complement_even
    {X : Type u} [Group X] [Finite X] {M Q : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M) (htM : t ∉ M)
    (hQ : IsNormalComplementIn M (M ⊓ rightConjugate M t) Q) :
    Even (Nat.card Q) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hQle : Q ≤ M := hQ.le_M
  have hDle : D ≤ M := by
    exact inf_le_left
  let QM : Subgroup M := Q.subgroupOf M
  let DM : Subgroup M := D.subgroupOf M
  haveI : QM.Normal := by
    simpa [QM] using hQ.normal_in_M
  have hdisjointM : Disjoint QM DM := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hQ.disjoint_D) hxQ hxD
  have hsupM : QM ⊔ DM = ⊤ := by
    calc
      QM ⊔ DM = (Q ⊔ D).subgroupOf M := by
        simpa [QM, DM] using
          (Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := M)
            hQle hDle).symm
      _ = M.subgroupOf M := by
        simpa [D] using congrArg (Subgroup.subgroupOf · M) hQ.sup_eq
      _ = ⊤ := Subgroup.subgroupOf_self M
  have hcomp : QM.IsComplement' DM :=
    isComplement'_of_disjoint_sup_eq_top_of_normal QM DM hdisjointM hsupM
  have hcard : Nat.card Q * Nat.card D = Nat.card M := by
    simpa [QM, DM, natCard_subgroupOf_eq Q M hQle,
      natCard_subgroupOf_eq D M hDle] using hcomp.card_mul
  have hprodEven : Even (Nat.card Q * Nat.card D) :=
    hcard.symm ▸ hM.card_even
  exact (Nat.even_mul.mp hprodEven).resolve_right
    (Nat.not_even_iff_odd.mpr (by
      simpa [D] using hM.inf_rightConjugate_card_odd htM))

/-- Normal-complement data for a distinct conjugate produce Peterfalvi's
standing hypothesis `(A1)` for the conjugate-coset action. -/
public theorem hypothesisA1_of_normal_complement
    {X : Type u} [Group X] [Finite X] {M Q : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (h2trans :
      MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hQ : IsNormalComplementIn M (M ⊓ rightConjugate M t) Q) :
    HypothesisA1 X (conjugateCosetSpace M)
      M (M ⊓ rightConjugate M t) Q t := by
  exact
    { two_transitive := h2trans
      point_stabilizer :=
        ⟨QuotientGroup.mk 1, (baseCoset_stabilizer M).symm⟩
      involution_t := ht
      t_not_mem_H := htM
      D_eq := rfl
      Q_le_H := hQ.le_M
      D_le_H := inf_le_left
      Q_normal_in_H := hQ.normal_in_M
      Q_disjoint_D := hQ.disjoint_D
      Q_sup_D := hQ.sup_eq
      Q_even := hM.normal_complement_even htM hQ
      D_odd := hM.inf_rightConjugate_card_odd htM }

/-- Adding faithfulness and ambient `2`-rank to the normal-complement data
produces the full hypothesis consumed by Suzuki recognition. -/
public theorem hypothesisA_of_normal_complement
    {X : Type u} [Group X] [Finite X] {M Q : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (h2trans :
      MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2)
    (hfaithful : FaithfulSMul X (conjugateCosetSpace M))
    (hrank : TwoRankAtLeastTwo X)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hQ : IsNormalComplementIn M (M ⊓ rightConjugate M t) Q) :
    HypothesisA X (conjugateCosetSpace M)
      M (M ⊓ rightConjugate M t) Q t := by
  exact
    { A1 := hM.hypothesisA1_of_normal_complement
        h2trans ht htM hQ
      A2 := hfaithful
      A3 := hrank }

/-- The supplied complement is nilpotent by the checked Peterfalvi Section 1
theorem once the full Suzuki hypotheses have been assembled. -/
public theorem normal_complement_nilpotent
    {X : Type u} [Group X] [Finite X] {M Q : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (h2trans :
      MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2)
    (hfaithful : FaithfulSMul X (conjugateCosetSpace M))
    (hrank : TwoRankAtLeastTwo X)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hQ : IsNormalComplementIn M (M ⊓ rightConjugate M t) Q) :
    Group.IsNilpotent Q := by
  exact PFchapter1section2.proposition_1_b_of_hA
    M (M ⊓ rightConjugate M t) Q t
    (hM.hypothesisA_of_normal_complement
      h2trans hfaithful hrank ht htM hQ)

end IsStronglyEmbedded
end CFSG.BenderSuzuki
