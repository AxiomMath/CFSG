module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Proposition111Action
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Proposition 11.1: fixed-point transport

The source invokes Lemma 8.3(b) after moving the base-fixed subgroup to the
reference pair of cosets.  This module proves that transport explicitly from
double transitivity, so the later Fitting argument does not assume a
conclusion-shaped containment.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- A subgroup of the base stabilizer with at least three fixed cosets can be
conjugated into the reference two-point stabilizer.  The conjugator is chosen
from the two-transitive action by sending the base/fixed pair to the
base/`t` pair. -/
public theorem proposition111_exists_rightConjugate_le_twoPointStabilizer
    {X : Type u} [Group X] [Finite X]
    {M Y : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (hYM : Y ≤ M)
    (hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Y)) :
    ∃ g : X, rightConjugate Y g ≤ M ⊓ rightConjugate M t := by
  classical
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let delta : conjugateCosetSpace M := QuotientGroup.mk t
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
    theorem4b_baseCoset_mem_fixedPoints hYM
  let alphaFixed : theorem4bFixedPoints M Y := ⟨alpha, halpha⟩
  have hnontrivial : Nontrivial (theorem4bFixedPoints M Y) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial (theorem4bFixedPoints M Y) := hnontrivial
  obtain ⟨betaFixed, hbetaNe⟩ := exists_ne alphaFixed
  let beta : conjugateCosetSpace M := betaFixed
  have hAlphaBeta : alpha ≠ beta := by
    intro h
    exact hbetaNe (Subtype.ext h.symm)
  have hAlphaDelta : alpha ≠ delta := by
    intro h
    apply htM
    simpa [alpha, delta] using QuotientGroup.eq.mp h
  rw [MulAction.is_two_pretransitive_iff] at htwo
  obtain ⟨x, hxAlpha, hxBeta⟩ :=
    htwo hAlphaBeta hAlphaDelta
  have hxM : x ∈ M := by
    have hxstab : x ∈ MulAction.stabilizer X alpha :=
      MulAction.mem_stabilizer_iff.mpr hxAlpha
    simpa [alpha] using hxstab
  have hYconjM : Y.conjBy x ≤ M := by
    have hmap : Y.conjBy x ≤ M.conjBy x := by
      exact Subgroup.map_mono hYM
    have hMconj : M.conjBy x = M :=
      section11_conjBy_eq_of_mem_normalizer (Subgroup.le_normalizer hxM)
    simpa [hMconj] using hmap
  have hYconjDelta : Y.conjBy x ≤ MulAction.stabilizer X delta := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hyY, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have hyBeta : y • beta = beta := betaFixed.property y hyY
    calc
      (x * y * x⁻¹) • delta = x • (y • beta) := by
        rw [← hxBeta]
        simp [mul_smul]
      _ = x • beta := by rw [hyBeta]
      _ = delta := hxBeta
  have hstabDelta : MulAction.stabilizer X delta = rightConjugate M t := by
    simpa [delta, ht.inv_eq_self] using conjugateCoset_stabilizer M t
  rw [hstabDelta] at hYconjDelta
  refine ⟨x⁻¹, ?_⟩
  simpa [rightConjugate] using le_inf hYconjM hYconjDelta

/-- The preceding pair transport followed by Lemma 8.3(b) places a subgroup
in the selected Peterfalvi fixed subgroup `V`. -/
public theorem proposition111_exists_rightConjugate_le_lemma83V
    {X : Type u} [Group X] [Finite X]
    {M Y : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (ht : IsInvolution t) (htM : t ∉ M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (hYM : Y ≤ M)
    (hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Y)) :
    ∃ g : X, rightConjugate Y g ≤
      peterfalviV (M ⊓ rightConjugate M t) t := by
  obtain ⟨g0, hg0⟩ :=
    proposition111_exists_rightConjugate_le_twoPointStabilizer
      ht htM htwo hYM hthree
  let Y0 : Subgroup X := rightConjugate Y g0
  have hcard0 : Nat.card (theorem4bFixedPoints M Y0) =
      Nat.card (theorem4bFixedPoints M Y) := by
    exact Nat.card_congr (theorem4bFixedPoints_rightConjugateEquiv M Y g0)
  have hthree0 : 3 ≤ Nat.card (theorem4bFixedPoints M Y0) := by
    rw [hcard0]
    exact hthree
  obtain ⟨g1, hg1D, hY0g1V⟩ := d83.conjugate_le Y0 hg0 hthree0
  refine ⟨g0 * g1, ?_⟩
  have hcomp : rightConjugate Y0 g1 =
      rightConjugate Y (g0 * g1) := by
    change (Y.conjBy g0⁻¹).conjBy g1⁻¹ = Y.conjBy (g0 * g1)⁻¹
    rw [Subgroup.conjBy_conjBy]
    simp [mul_inv_rev]
  rw [← hcomp]
  exact hY0g1V

end CFSG.BenderSuzuki
