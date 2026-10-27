module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5

namespace CFSG
end CFSG
open CFSG

/-!
# Isaacs Lemma 7.7

A source-faithful formulation of Isaacs, *Character Theory of Finite Groups*,
Lemma 7.7.  The T.I. hypothesis is written out rather than hidden behind a
new package: for every `g`, either the conjugate of `X` by `g` is `X`, or its
intersection with `X` is contained in `{1}`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.BenderSuzuki
namespace External
namespace Isaacs
namespace VII

private lemma sum_eq_sum_subgroup_of_supported
    {G M : Type*} [Group G] [Fintype G] [AddCommMonoid M]
    (H : Subgroup G) [Fintype H] (f : G -> M)
    (hzero : forall g : G, g ∉ H -> f g = 0) :
    (∑ g : G, f g) = ∑ h : H, f h := by
  classical
  let s : Finset G := Finset.univ.filter fun g : G => g ∈ H
  have hs : forall g : G, g ∈ s ↔ g ∈ H := by
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

private lemma mem_normalizer_of_conj_image_eq
    {G : Type*} [Group G] {X : Set G} {g : G}
    (hEq : ((fun x : G => g * x * g⁻¹) '' X) = X) :
    g ∈ Subgroup.normalizer X := by
  change forall x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X
  intro x
  constructor
  · intro hx
    have hximg : g * x * g⁻¹ ∈ ((fun y : G => g * y * g⁻¹) '' X) :=
      ⟨x, hx, rfl⟩
    simpa [hEq] using hximg
  · intro hx
    have hximg : g * x * g⁻¹ ∈ ((fun y : G => g * y * g⁻¹) '' X) := by
      simpa [hEq] using hx
    rcases hximg with ⟨y, hyX, hy⟩
    have hyx : y = x := by
      have hcong : g⁻¹ * (g * y * g⁻¹) * g = g⁻¹ * (g * x * g⁻¹) * g :=
        congrArg (fun z : G => g⁻¹ * z * g) hy
      simpa [mul_assoc] using hcong
    simpa [hyx] using hyX

private lemma mem_normalizer_of_mem_of_ti
    {G : Type*} [Group G] {X : Set G}
    (hTI : forall g : G,
      ((fun x : G => g * x * g⁻¹) '' X = X) \/
        (((fun x : G => g * x * g⁻¹) '' X) ∩ X ⊆ ({1} : Set G)))
    {x : G} (hx : x ∈ X) :
    x ∈ Subgroup.normalizer X := by
  rcases hTI x with hEq | hsmall
  · exact mem_normalizer_of_conj_image_eq hEq
  · have hximg : x ∈ ((fun y : G => x * y * x⁻¹) '' X) := by
      refine ⟨x, hx, ?_⟩
      group
    have hxone_mem : x ∈ ({1} : Set G) := hsmall ⟨hximg, hx⟩
    have hxone : x = 1 := by
      simpa using hxone_mem
    subst x
    change forall y : G, y ∈ X ↔ (1 : G) * y * (1 : G)⁻¹ ∈ X
    intro y
    simp

private lemma mem_normalizer_of_ti_conj_mem_ne_one
    {G : Type*} [Group G] {X : Set G}
    (hTI : forall g : G,
      ((fun x : G => g * x * g⁻¹) '' X = X) \/
        (((fun x : G => g * x * g⁻¹) '' X) ∩ X ⊆ ({1} : Set G)))
    {x y : G} (hx : x ∈ X) (hyx : y * x * y⁻¹ ∈ X)
    (hne : y * x * y⁻¹ ≠ 1) :
    y ∈ Subgroup.normalizer X := by
  rcases hTI y with hEq | hsmall
  · exact mem_normalizer_of_conj_image_eq hEq
  · have hyximg : y * x * y⁻¹ ∈ ((fun z : G => y * z * y⁻¹) '' X) :=
      ⟨x, hx, rfl⟩
    have hone_mem : y * x * y⁻¹ ∈ ({1} : Set G) := hsmall ⟨hyximg, hyx⟩
    have hone : y * x * y⁻¹ = 1 := by
      simpa using hone_mem
    exact False.elim (hne hone)

private lemma inducedCF_apply_of_isaacs_ti
    {G : Type*} [Group G] [Finite G] {X : Set G}
    (hTI : forall g : G,
      ((fun x : G => g * x * g⁻¹) '' X = X) \/
        (((fun x : G => g * x * g⁻¹) '' X) ∩ X ⊆ ({1} : Set G)))
    {theta : Section1.ClassFunction (Subgroup.normalizer X)}
    (hthetaClass : Section1.IsClassFunction theta)
    (hthetaVanish : forall n : Subgroup.normalizer X, (n : G) ∉ X -> theta n = 0)
    (hthetaOne : theta 1 = 0)
    {x : G} (hx : x ∈ X) :
    Section1.inducedCF (Subgroup.normalizer X) theta x =
      theta ⟨x, mem_normalizer_of_mem_of_ti hTI hx⟩ := by
  classical
  let N : Subgroup G := Subgroup.normalizer X
  let xN : N := ⟨x, mem_normalizer_of_mem_of_ti hTI hx⟩
  let f : G -> ℂ := fun y =>
    if hy : y * x * y⁻¹ ∈ N then theta ⟨y * x * y⁻¹, hy⟩ else 0
  have hzero : forall y : G, y ∉ N -> f y = 0 := by
    intro y hyN
    by_cases hyconjN : y * x * y⁻¹ ∈ N
    · by_cases hyconjX : y * x * y⁻¹ ∈ X
      · by_cases hone : y * x * y⁻¹ = 1
        · have hsub : (⟨y * x * y⁻¹, hyconjN⟩ : N) = 1 := by
            ext
            simpa using hone
          simp [f, hyconjN, hsub, hthetaOne]
        · have hynorm : y ∈ N :=
            mem_normalizer_of_ti_conj_mem_ne_one hTI hx hyconjX hone
          exact False.elim (hyN hynorm)
      · have hvanish : theta ⟨y * x * y⁻¹, hyconjN⟩ = 0 :=
          hthetaVanish ⟨y * x * y⁻¹, hyconjN⟩ hyconjX
        simp [f, hyconjN, hvanish]
    · simp [f, hyconjN]
  have hconst : forall y : N, f y = theta xN := by
    intro y
    have hyconjN : (y : G) * x * (y : G)⁻¹ ∈ N := by
      exact N.mul_mem (N.mul_mem y.2 xN.2) (N.inv_mem y.2)
    have hsub : (⟨(y : G) * x * (y : G)⁻¹, hyconjN⟩ : N) = y * xN * y⁻¹ := by
      ext
      rfl
    have hclass : theta ⟨(y : G) * x * (y : G)⁻¹, hyconjN⟩ = theta xN := by
      simpa [hsub] using hthetaClass y xN
    simp [f, hyconjN, hclass]
  have hsum : (∑ y : G, f y) = ∑ y : N, f y :=
    sum_eq_sum_subgroup_of_supported N f hzero
  have hsumConst : (∑ y : N, f y) = (Nat.card N : ℂ) * theta xN := by
    simp [hconst, Finset.card_univ]
  have hcardN : (Nat.card N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := N)).ne'
  unfold Section1.inducedCF Section1.inducedClassFunction
  change (Nat.card N : ℂ)⁻¹ * (∑ y : G, f y) = theta xN
  rw [hsum, hsumConst]
  field_simp [hcardN]

/-- Isaacs, Character Theory of Finite Groups, Lemma 7.7. -/
public theorem isaacs_lemma_7_7
    {G : Type*} [Group G] [Finite G] {X : Set G}
    (hTI : forall g : G,
      ((fun x : G => g * x * g⁻¹) '' X = X) \/
        (((fun x : G => g * x * g⁻¹) '' X) ∩ X ⊆ ({1} : Set G)))
    {phi theta : Section1.ClassFunction (Subgroup.normalizer X)}
    (_hphiClass : Section1.IsClassFunction phi)
    (hthetaClass : Section1.IsClassFunction theta)
    (hphiVanish : forall n : Subgroup.normalizer X, (n : G) ∉ X -> phi n = 0)
    (hthetaVanish : forall n : Subgroup.normalizer X, (n : G) ∉ X -> theta n = 0)
    (hthetaOne : theta 1 = 0) :
    (forall x : G, x ∈ X ->
      exists hxN : x ∈ Subgroup.normalizer X,
        Section1.inducedCF (Subgroup.normalizer X) theta x = theta ⟨x, hxN⟩) ∧
      Section1.scalarProduct G
          (Section1.inducedCF (Subgroup.normalizer X) theta)
          (Section1.inducedCF (Subgroup.normalizer X) phi) =
        Section1.scalarProduct (Subgroup.normalizer X) theta phi := by
  classical
  let N : Subgroup G := Subgroup.normalizer X
  constructor
  · intro x hx
    exact ⟨mem_normalizer_of_mem_of_ti hTI hx,
      inducedCF_apply_of_isaacs_ti hTI hthetaClass hthetaVanish hthetaOne hx⟩
  · have hfrob := Section1.inducedClassFunction_frobenius_right
      (H := N) phi (Section1.inducedCF N theta)
      (Section1.inducedCF_isClassFunction N theta)
    rw [hfrob]
    unfold Section1.scalarProduct Section1.subgroupRestriction
    congr 1
    refine Finset.sum_congr rfl ?_
    intro n _hn
    by_cases hnX : (n : G) ∈ X
    · have happ := inducedCF_apply_of_isaacs_ti hTI hthetaClass hthetaVanish hthetaOne hnX
      have hnEq : (⟨(n : G), mem_normalizer_of_mem_of_ti hTI hnX⟩ : N) = n := by
        ext
        rfl
      simpa [N, hnEq] using congrArg (fun z => z * star (phi n)) happ
    · have hphiZero : phi n = 0 := hphiVanish n hnX
      simp [hphiZero]

end VII
end Isaacs
end External
end CFSG.BenderSuzuki



