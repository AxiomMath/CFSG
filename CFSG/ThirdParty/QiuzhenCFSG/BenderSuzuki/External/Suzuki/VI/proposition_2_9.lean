module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.proposition_2_8
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.CharacterValues
import Mathlib.Tactic.Group

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki VI.(2.9)

Induction preserves values and the stated scalar products for generalized
characters supported on a trivial-intersection subset.
-/

noncomputable section

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace VI

universe u

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

private lemma sum_eq_sum_subgroup_of_supported_29
    {G M : Type*} [Group G] [Fintype G] [AddCommMonoid M]
    (H : Subgroup G) [Fintype H] (f : G → M)
    (hzero : ∀ g : G, g ∉ H → f g = 0) :
    (∑ g : G, f g) = ∑ h : H, f h := by
  classical
  let s : Finset G := Finset.univ.filter fun g : G => g ∈ H
  have hs : ∀ g : G, g ∈ s ↔ g ∈ H := by
    intro g
    simp [s]
  have hsub : ∑ g ∈ s, f g = ∑ h : H, f h :=
    Finset.sum_subtype (s := s) (p := fun g : G => g ∈ H) hs f
  calc
    (∑ g : G, f g) = ∑ g : G, if g ∈ H then f g else 0 := by
      refine Finset.sum_congr rfl ?_
      intro g _hg
      by_cases hgH : g ∈ H
      · simp [hgH]
      · simp [hgH, hzero g hgH]
    _ = ∑ g ∈ s, f g := by
      simpa [s] using
        (Finset.sum_filter (s := (Finset.univ : Finset G))
          (p := fun g : G => g ∈ H) f).symm
    _ = ∑ h : H, f h := hsub

private lemma inducedCF_apply_of_suzuki_ti_ne_one
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (K : Set G)
    (hTI : IsTISubsetRelative H K)
    {theta : Section1.ClassFunction H}
    (hthetaClass : Section1.IsClassFunction theta)
    (hthetaSupport : ∀ h : H, (h : G) ∉ K → theta h = 0)
    {x : G} (hx : x ∈ K) (hxne : x ≠ 1) :
    Section1.inducedCF H theta x = theta ⟨x, hTI.1 hx⟩ := by
  classical
  let xH : H := ⟨x, hTI.1 hx⟩
  let f : G → ℂ := fun y =>
    if hy : y * x * y⁻¹ ∈ H then theta ⟨y * x * y⁻¹, hy⟩ else 0
  have hzero : ∀ y : G, y ∉ H → f y = 0 := by
    intro y hyH
    by_cases hyconjH : y * x * y⁻¹ ∈ H
    · by_cases hyconjK : y * x * y⁻¹ ∈ K
      · obtain ⟨h, hh⟩ := hTI.2.2.1 hx hyconjK ⟨y, rfl⟩
        have hc : (h : G)⁻¹ * y ∈ Subgroup.centralizer ({x} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          have ha_eq : a = x := by simpa using ha
          subst a
          calc
            x * ((h : G)⁻¹ * y) =
                (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * y := by group
            _ = (h : G)⁻¹ * (y * x * y⁻¹) * y := by rw [hh]
            _ = ((h : G)⁻¹ * y) * x := by group
        have hcH : (h : G)⁻¹ * y ∈ H :=
          hTI.2.2.2 x hx hxne hc
        have hyH' : y ∈ H := by
          have := H.mul_mem h.property hcH
          simpa using this
        exact False.elim (hyH hyH')
      · have hvanish :
            theta ⟨y * x * y⁻¹, hyconjH⟩ = 0 :=
          hthetaSupport ⟨y * x * y⁻¹, hyconjH⟩ hyconjK
        simp [f, hyconjH, hvanish]
    · simp [f, hyconjH]
  have hconst : ∀ y : H, f y = theta xH := by
    intro y
    have hyconjH : (y : G) * x * (y : G)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem y.property xH.property) (H.inv_mem y.property)
    have hsub :
        (⟨(y : G) * x * (y : G)⁻¹, hyconjH⟩ : H) =
          y * xH * y⁻¹ := by
      ext
      rfl
    have hclass :
        theta ⟨(y : G) * x * (y : G)⁻¹, hyconjH⟩ = theta xH := by
      simpa [hsub] using hthetaClass y xH
    simp [f, hyconjH, hclass]
  have hsum : (∑ y : G, f y) = ∑ y : H, f y :=
    sum_eq_sum_subgroup_of_supported_29 H f hzero
  have hsumConst : (∑ y : H, f y) = (Nat.card H : ℂ) * theta xH := by
    simp [hconst, Finset.card_univ]
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  unfold Section1.inducedCF Section1.inducedClassFunction
  change (Nat.card H : ℂ)⁻¹ * (∑ y : G, f y) = theta xH
  rw [hsum, hsumConst]
  field_simp [hcardH]

/-- Suzuki, *Group Theory II*, Chapter 6, (2.9). -/
public theorem suzuki_ch6_proposition_2_9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (K : Set G)
    (hTI : IsTISubsetRelative H K)
    (theta : Section1.ClassFunction H)
    (hthetaVirtual : Theory.Character.IsVirtualCharacter theta)
    (hthetaSupport : ∀ h : H, (h : G) ∉ K → theta h = 0) :
    (∀ (x : G) (hx : x ∈ K), x ≠ 1 →
      Section1.inducedCF H theta x = theta ⟨x, hTI.1 hx⟩) ∧
    Section1.scalarProduct G (Section1.inducedCF H theta)
        (Section1.principalCharacter G) =
      Section1.scalarProduct H theta (Section1.principalCharacter H) ∧
    (theta 1 = 0 →
      ∀ phi : Section1.ClassFunction H,
        Theory.Character.IsVirtualCharacter phi →
        (∀ h : H, (h : G) ∉ K → phi h = 0) →
        Section1.scalarProduct G (Section1.inducedCF H theta)
            (Section1.inducedCF H phi) =
          Section1.scalarProduct H theta phi) := by
  classical
  have hthetaClass : Section1.IsClassFunction theta :=
    Section1.isVirtualCharacter_isClassFunction hthetaVirtual
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hxne
    exact inducedCF_apply_of_suzuki_ti_ne_one
      H K hTI hthetaClass hthetaSupport hx hxne
  · have hprincipalClass :
        Section1.IsClassFunction (Section1.principalCharacter G) := by
      intro x g
      rfl
    have hprincipalRestriction :
        Section1.subgroupRestriction H (Section1.principalCharacter G) =
          Section1.principalCharacter H := by
      ext h
      rfl
    rw [Section1.inducedClassFunction_frobenius_general
      H theta (Section1.principalCharacter G) hprincipalClass,
      hprincipalRestriction]
  · intro hthetaOne phi hphiVirtual hphiSupport
    have hphiClass : Section1.IsClassFunction phi :=
      Section1.isVirtualCharacter_isClassFunction hphiVirtual
    rw [Section1.inducedClassFunction_frobenius_general
      H theta (Section1.inducedCF H phi)
        (Section1.inducedCF_isClassFunction H phi)]
    unfold Section1.scalarProduct Section1.subgroupRestriction
    congr 1
    refine Finset.sum_congr rfl ?_
    intro h _hh
    by_cases hhK : (h : G) ∈ K
    · by_cases hhOne : h = 1
      · subst h
        simp [hthetaOne]
      · have hhOneG : (h : G) ≠ 1 := by
          intro hh
          apply hhOne
          apply Subtype.ext
          simpa using hh
        have happ := inducedCF_apply_of_suzuki_ti_ne_one
          H K hTI hphiClass hphiSupport hhK hhOneG
        have hsub : (⟨(h : G), hTI.1 hhK⟩ : H) = h := by
          ext
          rfl
        simpa [hsub] using congrArg (fun z => theta h * star z) happ
    · have hthetaZero : theta h = 0 := hthetaSupport h hhK
      simp [hthetaZero]

end VI
end Suzuki
end External
end CFSG.BenderSuzuki
