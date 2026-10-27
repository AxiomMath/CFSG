module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Mathlib.GroupTheory.IsSubnormal

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 8.4 consumer lemmas

The full source-facing statement is `Proposition84Statement` in
`SE.Interfaces`.  This module derives the smaller normalizer package used by
Sections 9 and 11 from that full statement.  No Proposition 8.4 conclusion is
assumed here.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The normalizer factor supplied by the part of Proposition 8.4 used in
Lemmas 9.4 and 11.2.

Here `N_M(Y) = M ⊓ N_X(Y)` and `N_D(Y) = D ⊓ N_X(Y)`.  The source
subgroup `S` is a normal `2`-subgroup of `N_M(Y)`, lies in `C_X(Y)`, and
gives the set-product factorization `N_M(Y) = S N_D(Y)`. -/
public structure Proposition84NormalizerFactor
    {X : Type u} [Group X]
    (M D Y S : Subgroup X) : Prop where
  le_normalizerIn : S ≤ M ⊓ Subgroup.normalizer (Y : Set X)
  le_centralizer : S ≤ Subgroup.centralizer (Y : Set X)
  isPGroup_two : IsPGroup 2 S
  normal_in_normalizerIn :
    (S.subgroupOf (M ⊓ Subgroup.normalizer (Y : Set X))).Normal
  normalizerIn_eq_mul :
    ((M ⊓ Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) =
      (S : Set X) *
        ((D ⊓ Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X)

namespace Proposition84NormalizerFactor

/-- The Proposition 8.4 factor lies in `M`. -/
public theorem le_M
    {X : Type u} [Group X] {M D Y S : Subgroup X}
    (hS : Proposition84NormalizerFactor M D Y S) : S ≤ M :=
  hS.le_normalizerIn.trans inf_le_left

/-- The Proposition 8.4 factor normalizes `Y`. -/
public theorem le_normalizer
    {X : Type u} [Group X] {M D Y S : Subgroup X}
    (hS : Proposition84NormalizerFactor M D Y S) :
    S ≤ Subgroup.normalizer (Y : Set X) :=
  hS.le_normalizerIn.trans inf_le_right

end Proposition84NormalizerFactor

public theorem centralizerTwoPrimeResidual_le_centralizer
    {X : Type u} [Group X] (Y : Subgroup X) :
    centralizerTwoPrimeResidual Y ≤ Subgroup.centralizer (Y : Set X) := by
  dsimp [centralizerTwoPrimeResidual]
  exact Subgroup.map_subtype_le _

namespace Proposition84Statement

/-- Apply the full Proposition 8.4 statement using the
`V = C_D(t) = C_D(u)` identification stored by Lemma 8.3, and extract the
normalizer factor needed later. -/
public theorem exists_factor
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {t : X} (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    {Y Y₁ : Subgroup X}
    (hYV :
      Y ≤ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({t} : Set X))
    (hY₁ : Y₁ ≠ ⊥) (hY₁Y : Y₁ ≤ Y)
    (hsubnormal : (Y₁.subgroupOf Y).IsSubnormal)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y₁) :
    ∃ S : Subgroup X,
      Proposition84NormalizerFactor
        M (M ⊓ rightConjugate M t) Y S := by
  have hYVu :
      Y ≤ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X) := by
    rw [← d83.centralizer_eq]
    exact hYV
  obtain ⟨hAB, _hCD⟩ :=
    h84 Y Y₁ hYVu hY₁ hY₁Y hsubnormal hI
  dsimp [Proposition84ABConclusion] at hAB
  rcases hAB with
    ⟨_hTwoTransitive, _hNormalizer, S, hSle, hSnormal,
      hSsylow, _hSregular, hFactor⟩
  refine ⟨S, ?_⟩
  refine
    { le_normalizerIn := ?_
      le_centralizer := ?_
      isPGroup_two := ?_
      normal_in_normalizerIn := ?_
      normalizerIn_eq_mul := ?_ }
  · simpa [normalizerIn] using hSle
  · obtain ⟨P, rfl⟩ := hSsylow
    exact (Subgroup.map_subtype_le (P : Subgroup
      ↥(centralizerTwoPrimeResidual Y ⊓ M))).trans
      (inf_le_left.trans (centralizerTwoPrimeResidual_le_centralizer Y))
  · obtain ⟨P, rfl⟩ := hSsylow
    exact P.isPGroup'.map
      (centralizerTwoPrimeResidual Y ⊓ M).subtype
  · change (S.subgroupOf (normalizerIn M Y)).Normal
    exact hSnormal
  · simpa [normalizerIn] using hFactor

/-- A normal subgroup is subnormal, giving the common Proposition 8.4
application used in Sections 9 and 11. -/
public theorem exists_factor_of_normal
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {t : X} (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    {Y Y₁ : Subgroup X}
    (hYV :
      Y ≤ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({t} : Set X))
    (hY₁ : Y₁ ≠ ⊥) (hY₁Y : Y₁ ≤ Y)
    (hnormal : (Y₁.subgroupOf Y).Normal)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y₁) :
    ∃ S : Subgroup X,
      Proposition84NormalizerFactor
        M (M ⊓ rightConjugate M t) Y S := by
  exact h84.exists_factor d83 hYV hY₁ hY₁Y
    hnormal.isSubnormal hI

end Proposition84Statement

end CFSG.BenderSuzuki
