module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Proposition111Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Action
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingFusion

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Proposition 11.1: fixed-point cardinality core

The source uses semiregularity of `B₁` on the conjugate-coset action to get at
least `|B₁|` fixed points for `C_M(B₁)`.  This file records that orbit
injection independently of Proposition 11.1 itself.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u v

/-- A semiregular subgroup orbit of a base point injects into the fixed points
of any subgroup which centralizes it. -/
public theorem proposition111_card_fixedPoints_of_semiregular_centralizer
    {X : Type u} {Omega : Type v} [Group X] [Finite X]
    [MulAction X Omega] [Finite Omega]
    {B Y : Subgroup X} (alpha : Omega)
    (hYalpha : Y ≤ MulAction.stabilizer X alpha)
    (hBC : B ≤ Subgroup.centralizer (Y : Set X))
    (hsemireg : ∀ b : B, (b : X) • alpha = alpha → b = 1) :
    Nat.card B ≤ Nat.card (fixedPointsOfSubgroup X Omega Y) := by
  let f : B → fixedPointsOfSubgroup X Omega Y := fun b =>
    ⟨(b : X) • alpha,
      smul_mem_fixedPointsOfSubgroup_of_mem_centralizer
        (hBC b.property) (by
          intro y hyY
          exact MulAction.mem_stabilizer_iff.mp (hYalpha hyY))⟩
  have hf : Function.Injective f := by
    intro b c hbc
    have hsmul : (b : X) • alpha = (c : X) • alpha :=
      congrArg Subtype.val hbc
    have hfix : ((c : X)⁻¹ * (b : X)) • alpha = alpha := by
      rw [mul_smul, inv_smul_eq_iff]
      exact hsmul
    have hmem : ((c : X)⁻¹ * (b : X)) ∈ B := by
      exact B.mul_mem (B.inv_mem c.property) b.property
    have hone : (⟨(c : X)⁻¹ * (b : X), hmem⟩ : B) = 1 :=
      hsemireg ⟨(c : X)⁻¹ * (b : X), hmem⟩ hfix
    have hone' : (c : X)⁻¹ * (b : X) = 1 := congrArg Subtype.val hone
    exact Subtype.ext ((inv_mul_eq_one.mp hone').symm)
  exact Nat.card_le_card_of_injective f hf

/-- Empty fixed-point sets for every nonidentity element give semiregularity
at each point. -/
public theorem proposition111_semiregular_at_of_nonidentity_fixedPoints_empty
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (B : Subgroup X)
    (hfix : ∀ x : X, x ∈ B → x ≠ 1 →
      fixedPointsOfSubgroup X Omega (Subgroup.zpowers x) = ∅)
    (alpha : Omega) :
    ∀ b : B, (b : X) • alpha = alpha → b = 1 := by
  intro b hb
  by_contra hbne
  have hbneX : (b : X) ≠ 1 := by
    intro hbone
    exact hbne (Subtype.ext hbone)
  have hmem : alpha ∈
      fixedPointsOfSubgroup X Omega (Subgroup.zpowers (b : X)) :=
    mem_fixedPointsOfSubgroup_zpowers_iff.mpr hb
  rw [hfix (b : X) b.property hbneX] at hmem
  exact hmem

/-- Source `(11A)` fixed-point lower bound: if every nonidentity element of
`B` is semiregular on the conjugate-coset action, then `C_M(B)` fixes at
least `|B|` cosets. -/
public theorem proposition111_card_le_fixedPoints_subgroupCentralizerIn
    {X : Type u} [Group X] [Finite X]
    (M B : Subgroup X)
    (hfix : ∀ x : X, x ∈ B → x ≠ 1 →
      fixedPointsOfSubgroup X (conjugateCosetSpace M)
        (Subgroup.zpowers x) = ∅) :
    Nat.card B ≤
      Nat.card (theorem4bFixedPoints M (subgroupCentralizerIn M B)) := by
  let Y : Subgroup X := subgroupCentralizerIn M B
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  have hYalpha : Y ≤ MulAction.stabilizer X alpha := by
    intro y hy
    rw [show MulAction.stabilizer X alpha = M by
      simp [alpha]]
    exact hy.1
  have hBC : B ≤ Subgroup.centralizer (Y : Set X) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hyY
    exact ((Subgroup.mem_centralizer_iff.mp hyY.2) b hb).symm
  exact proposition111_card_fixedPoints_of_semiregular_centralizer
    alpha hYalpha hBC
      (proposition111_semiregular_at_of_nonidentity_fixedPoints_empty
        B hfix alpha)

end CFSG.BenderSuzuki
