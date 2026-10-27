module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.6)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_6.tex`.

Current scope discipline:

* Proposition (1.5) is imported from `PFtest`; all other imports are Mathlib.
* No Lean files outside `PFtest` are imported or read.
* This file currently records honest kernel-stability infrastructure for
  Proposition (1.6).
* Part (a) is exposed as the public theorem `proposition_1_6_a`.
* The current quotient part is only a private conditional helper: it assumes
  the quotient-side class functions and their pullback equations instead of
  constructing them from `A ≤ Ker θ`, so it is not counted as book-facing
  Proposition (1.6.b).
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section1
universe u
universe v

/-! ## Basic notation for Proposition (1.6) -/

@[expose] public def subgroupInKernel' {G : Type*} [Group G]
    (phi : ClassFunction G) (A : Subgroup G) : Prop :=
  ∀ a : A, phi a = degree phi

@[expose] public def subgroupInRepresentationKernel
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) : Prop :=
  ∀ a : A, ρ (a : G) = 1


/-! ## Honest kernel-transport lemmas -/


public lemma subgroupInKernel'_of_eq
    {G : Type*} [Group G]
    {phi psi : ClassFunction G} {A : Subgroup G}
    (hEq : phi = psi) (hA : subgroupInKernel' phi A) :
    subgroupInKernel' psi A := by
  subst hEq
  exact hA


lemma subgroupInKernel'_smul
    {G : Type*} [Group G] (z : ℂ) (phi : ClassFunction G) (A : Subgroup G)
    (hA : subgroupInKernel' phi A) :
    subgroupInKernel' (z • phi) A := by
  intro a
  simp [degree, hA a]

lemma subgroupInKernel'_of_smul_ne_zero
    {G : Type*} [Group G] {z : ℂ} (hz : z ≠ 0)
    (phi : ClassFunction G) (A : Subgroup G)
    (hA : subgroupInKernel' (z • phi) A) :
    subgroupInKernel' phi A := by
  intro a
  have h := hA a
  have hmul : z * phi a = z * phi 1 := by
    simpa [degree] using h
  exact mul_left_cancel₀ hz hmul

lemma subgroupInKernel'_fintype_sum
    {G ι : Type*} [Group G] [Finite ι]
    (Phi : ι → ClassFunction G) (A : Subgroup G)
    (hA : ∀ i, subgroupInKernel' (Phi i) A) :
    subgroupInKernel' (fun g => ∑ i, Phi i g) A := by
  intro a
  calc
    (∑ i : ι, Phi i a) = ∑ i : ι, Phi i 1 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [degree] using hA i a
    _ = degree (fun g => ∑ i : ι, Phi i g) := by
      simp [degree]

lemma subgroupInKernel'_subgroupRestriction_iff
    {G : Type*} [Group G] (H A : Subgroup G) (hAH : A ≤ H)
    (phi : ClassFunction G) :
    subgroupInKernel' (subgroupRestriction H phi) (A.subgroupOf H) ↔ subgroupInKernel' phi A := by
  constructor
  · intro h a
    have haH : a.1 ∈ H := hAH a.2
    have hs : (⟨a.1, haH⟩ : H) ∈ A.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      simp [a.2]
    have h' := h ⟨⟨a.1, haH⟩, hs⟩
    simp [subgroupRestriction, degree] at h' ⊢
    exact h'
  · intro h a
    simpa [subgroupRestriction, degree] using h ⟨a.1, a.2⟩

@[expose] public def quotientImageSubgroup
    {G : Type*} [Group G] (H A : Subgroup G) [A.Normal] :
    Subgroup (G ⧸ A) :=
  H.map (QuotientGroup.mk' A)

public instance quotientImageSubgroup_normal
    {G : Type*} [Group G] (H A : Subgroup G) [A.Normal] [H.Normal] :
    (quotientImageSubgroup H A).Normal := by
  dsimp [quotientImageSubgroup]
  infer_instance

lemma quotientImageSubgroup_mk_mem
    {G : Type*} [Group G] (H A : Subgroup G) [A.Normal]
    {g : G} (hg : g ∈ H) :
    (QuotientGroup.mk' A g : G ⧸ A) ∈ quotientImageSubgroup H A := by
  exact ⟨g, hg, rfl⟩

theorem quotientImageSubgroup_mk_mem_iff
    {G : Type*} [Group G] (H A : Subgroup G) [A.Normal]
    (hAH : A ≤ H) (g : G) :
    (QuotientGroup.mk' A g : G ⧸ A) ∈ quotientImageSubgroup H A ↔ g ∈ H := by
  constructor
  · rintro ⟨x, hxH, hxq⟩
    have hxdiv : x / g ∈ A := by
      exact (QuotientGroup.eq_iff_div_mem).mp hxq
    have hxgA : x * g⁻¹ ∈ A := by
      simpa [div_eq_mul_inv] using hxdiv
    have hxgH : x * g⁻¹ ∈ H := hAH hxgA
    have hg_inv : g⁻¹ ∈ H := by
      simpa [div_eq_mul_inv, mul_assoc] using H.mul_mem (H.inv_mem hxH) hxgH
    exact (Subgroup.inv_mem_iff H).mp hg_inv
  · intro hg
    exact quotientImageSubgroup_mk_mem H A hg

private lemma mem_subgroup_iff_conj_mem
    {G : Type*} [Group G] (H : Subgroup G) [hH : H.Normal]
    (x g : G) :
    x * g * x⁻¹ ∈ H ↔ g ∈ H := by
  constructor
  · intro hx
    have hx' : x⁻¹ * (x * g * x⁻¹) * x ∈ H := by
      simpa [mul_assoc] using hH.conj_mem (x * g * x⁻¹) hx x⁻¹
    simpa [mul_assoc] using hx'
  · intro hg
    simpa using hH.conj_mem g hg x

private lemma inducedClassFunction_formula_on_subgroup
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) (h : H) :
    inducedClassFunction H theta h =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G,
        theta ⟨x * h.1 * x⁻¹, hH.conj_mem h.1 h.2 x⟩ := by
  classical
  unfold inducedClassFunction
  refine congrArg ((Nat.card H : ℂ)⁻¹ * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxtrue : x * h.1 * x⁻¹ ∈ H := hH.conj_mem h.1 h.2 x
  simp [hxtrue]

private lemma inducedClassFunction_eq_zero_of_not_mem
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) {g : G} (hg : g ∉ H) :
    inducedClassFunction H theta g = 0 := by
  classical
  unfold inducedClassFunction
  have hsum :
      ∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) =
        0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxfalse : ¬ x * g * x⁻¹ ∈ H := by
      rw [mem_subgroup_iff_conj_mem H x g]
      exact hg
    simp [hxfalse]
  rw [hsum]
  simp

private lemma inducedClassFunction_supportedOnSubgroup
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) :
    supportedOnSubgroup (inducedClassFunction H theta) H := by
  intro g hg
  exact inducedClassFunction_eq_zero_of_not_mem H theta hg

public lemma degree_conjugateOnNormal
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (g : G) :
    degree (conjugateOnNormal H theta g) = degree theta := by
  unfold degree conjugateOnNormal
  exact congrArg theta (Subtype.ext (by simp))

private lemma conjugateOrbit_base_eq_theta
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) :
    conjugateOrbitConj H theta (conjugateOrbitFiber H theta 1) = theta := by
  funext h
  simp [conjugateOrbitConj, conjugateOrbitFiber, conjugateOnNormal]

private lemma relIndex_inertia_ne_zero
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (theta : ClassFunction H) :
    H.relIndex (inertiaSubgroup H theta) ≠ 0 := by
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem quotient_inducedCF_supported
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [A.Normal] [H.Normal]
    (thetaQuot : ClassFunction (quotientImageSubgroup H A)) :
    supportedOnSubgroup
      (inducedCF (quotientImageSubgroup H A) thetaQuot)
      (quotientImageSubgroup H A) := by
  exact inducedClassFunction_supportedOnSubgroup
    (quotientImageSubgroup H A) thetaQuot

theorem quotient_lift_inducedCF_supported
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [A.Normal] [H.Normal] (_hAH : A ≤ H)
    (theta : ClassFunction H) (chiQuot : ClassFunction (G ⧸ A))
    (hchiQuot :
      ∀ g : G, chiQuot (QuotientGroup.mk' A g) = inducedCF H theta g) :
    supportedOnSubgroup chiQuot (quotientImageSubgroup H A) := by
  intro q hq
  rcases QuotientGroup.mk'_surjective A q with ⟨g, rfl⟩
  have hgH : g ∉ H := by
    intro hg
    exact hq (quotientImageSubgroup_mk_mem H A hg)
  rw [hchiQuot g]
  exact inducedClassFunction_eq_zero_of_not_mem H theta hgH

lemma quotient_mk_fiber_nat_card
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (q : G ⧸ A) :
    Nat.card {x : G // ((x : G ⧸ A) = q)} = Nat.card A := by
  classical
  letI : Fintype (G ⧸ A) := Fintype.ofFinite (G ⧸ A)
  calc
    Nat.card {x : G // ((x : G ⧸ A) = q)} =
        Nat.card (A × ({q} : Set (G ⧸ A))) := by
      exact Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet A ({q}))
    _ = Nat.card A := by
      simp

lemma quotient_sum_lift
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (F : G ⧸ A → ℂ) :
    (∑ x : G, F ((x : G ⧸ A))) =
      (Nat.card A : ℂ) * (∑ q : G ⧸ A, F q) := by
  classical
  letI : Fintype (G ⧸ A) := Fintype.ofFinite (G ⧸ A)
  letI : Fintype G := Fintype.ofFinite G
  calc
    (∑ x : G, F ((x : G ⧸ A))) =
        ∑ q : G ⧸ A, ∑ x : {x : G // ((x : G ⧸ A) = q)},
          F ((x : G ⧸ A)) := by
      exact (Fintype.sum_fiberwise (g := fun x : G => (x : G ⧸ A))
        (f := fun x : G => F ((x : G ⧸ A)))).symm
    _ = ∑ q : G ⧸ A, ∑ _x : {x : G // ((x : G ⧸ A) = q)}, F q := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp [x.2]
    _ = ∑ q : G ⧸ A, (Nat.card A : ℂ) * F q := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rw [← quotient_mk_fiber_nat_card A q]
      simp
    _ = (Nat.card A : ℂ) * (∑ q : G ⧸ A, F q) := by
      rw [Finset.mul_sum]

lemma quotientImageSubgroup_card
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [A.Normal] (hAH : A ≤ H) :
    Nat.card H = Nat.card (quotientImageSubgroup H A) * Nat.card A := by
  classical
  let f : H →* G ⧸ A := (QuotientGroup.mk' A).comp H.subtype
  have hker : f.ker = A.subgroupOf H := by
    ext h
    change (((h : G) : G ⧸ A) = 1) ↔ (h : G) ∈ A
    exact QuotientGroup.eq_one_iff (N := A) (h : G)
  have hrange : f.range = quotientImageSubgroup H A := by
    ext q
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨(h : G), h.2, rfl⟩
    · rintro ⟨g, hgH, rfl⟩
      exact ⟨⟨g, hgH⟩, rfl⟩
  have hsubcard : Nat.card (A.subgroupOf H) = Nat.card A := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hquotcard :
      Nat.card (H ⧸ A.subgroupOf H) = Nat.card (quotientImageSubgroup H A) := by
    calc
      Nat.card (H ⧸ A.subgroupOf H) = Nat.card (H ⧸ f.ker) := by
        rw [hker]
      _ = Nat.card f.range := by
        exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (φ := f)).toEquiv
      _ = Nat.card (quotientImageSubgroup H A) := by
        rw [hrange]
  calc
    Nat.card H = Nat.card (H ⧸ A.subgroupOf H) * Nat.card (A.subgroupOf H) := by
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf H)
    _ = Nat.card (quotientImageSubgroup H A) * Nat.card A := by
      rw [hquotcard, hsubcard]

public theorem inducedCF_principal_quotientImageSubgroup_mk
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [A.Normal] (hAH : A ≤ H)
    (g : G) :
    inducedCF H (principalCharacter H) g =
      inducedCF (quotientImageSubgroup H A)
        (principalCharacter (quotientImageSubgroup H A))
        (QuotientGroup.mk' A g) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (G ⧸ A) := Fintype.ofFinite (G ⧸ A)
  let B : Subgroup (G ⧸ A) := quotientImageSubgroup H A
  let qg : G ⧸ A := QuotientGroup.mk' A g
  let F : G ⧸ A → ℂ := fun y =>
    if y * qg * y⁻¹ ∈ B then (1 : ℂ) else 0
  have hterm : ∀ x : G,
      (if hx : x * g * x⁻¹ ∈ H then
        principalCharacter H ⟨x * g * x⁻¹, hx⟩
      else
        0) = F (QuotientGroup.mk' A x) := by
    intro x
    have hmem :
        (QuotientGroup.mk' A x) * qg * (QuotientGroup.mk' A x)⁻¹ ∈ B ↔
          x * g * x⁻¹ ∈ H := by
      simpa [B, qg, quotientImageSubgroup] using
        (quotientImageSubgroup_mk_mem_iff H A hAH (x * g * x⁻¹))
    by_cases hx : x * g * x⁻¹ ∈ H
    · have hxq :
          (QuotientGroup.mk' A x) * qg * (QuotientGroup.mk' A x)⁻¹ ∈ B :=
        hmem.2 hx
      have hxq' : (x : G ⧸ A) * qg * (x : G ⧸ A)⁻¹ ∈ B := by
        simpa using hxq
      simp [principalCharacter, hx]
      change (1 : ℂ) =
        if (x : G ⧸ A) * qg * (x : G ⧸ A)⁻¹ ∈ B then 1 else 0
      simp [hxq']
    · have hxq :
          ¬ (QuotientGroup.mk' A x) * qg * (QuotientGroup.mk' A x)⁻¹ ∈ B :=
        mt hmem.1 hx
      have hxq' : ¬ (x : G ⧸ A) * qg * (x : G ⧸ A)⁻¹ ∈ B := by
        simpa using hxq
      simp [hx]
      change (0 : ℂ) =
        if (x : G ⧸ A) * qg * (x : G ⧸ A)⁻¹ ∈ B then 1 else 0
      simp [hxq']
  have hsum_lift :
      (∑ x : G,
        (if hx : x * g * x⁻¹ ∈ H then
          principalCharacter H ⟨x * g * x⁻¹, hx⟩
        else
          0)) =
        (Nat.card A : ℂ) * (∑ y : G ⧸ A, F y) := by
    calc
      (∑ x : G,
        (if hx : x * g * x⁻¹ ∈ H then
          principalCharacter H ⟨x * g * x⁻¹, hx⟩
        else
          0)) =
          ∑ x : G, F (QuotientGroup.mk' A x) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            exact hterm x
      _ = (Nat.card A : ℂ) * (∑ y : G ⧸ A, F y) :=
            quotient_sum_lift A F
  have hsum_quot :
      (∑ y : G ⧸ A,
        (if hy : y * QuotientGroup.mk' A g * y⁻¹ ∈ quotientImageSubgroup H A then
          principalCharacter (quotientImageSubgroup H A)
            ⟨y * QuotientGroup.mk' A g * y⁻¹, hy⟩
        else
          0)) =
        ∑ y : G ⧸ A, F y := by
    refine Finset.sum_congr rfl ?_
    intro y _hy
    by_cases hyB : y * QuotientGroup.mk' A g * y⁻¹ ∈ quotientImageSubgroup H A
    · simp [F, B, qg]
      rfl
    · simp [F, B, qg]
      rfl
  have hcard : Nat.card H = Nat.card B * Nat.card A := by
    simpa [B] using quotientImageSubgroup_card H A hAH
  have hA_ne : (Nat.card A : ℂ) ≠ 0 := by
    exact_mod_cast
      (Nat.card_ne_zero.mpr ⟨⟨1, A.one_mem⟩, inferInstance⟩ : Nat.card A ≠ 0)
  have hB_ne : (Nat.card B : ℂ) ≠ 0 := by
    exact_mod_cast
      (Nat.card_ne_zero.mpr ⟨⟨1, B.one_mem⟩, inferInstance⟩ : Nat.card B ≠ 0)
  calc
    inducedCF H (principalCharacter H) g =
        (Nat.card H : ℂ)⁻¹ *
          (∑ x : G,
            (if hx : x * g * x⁻¹ ∈ H then
              principalCharacter H ⟨x * g * x⁻¹, hx⟩
            else
              0)) := by
          rfl
    _ = (Nat.card H : ℂ)⁻¹ *
          ((Nat.card A : ℂ) * (∑ y : G ⧸ A, F y)) := by
          rw [hsum_lift]
    _ = (Nat.card B : ℂ)⁻¹ * (∑ y : G ⧸ A, F y) := by
          have hcardC : (Nat.card H : ℂ) =
              (Nat.card B : ℂ) * (Nat.card A : ℂ) := by
            exact_mod_cast hcard
          rw [hcardC]
          field_simp [hA_ne, hB_ne]
    _ = inducedCF (quotientImageSubgroup H A)
          (principalCharacter (quotientImageSubgroup H A))
          (QuotientGroup.mk' A g) := by
          rw [inducedCF, inducedClassFunction, hsum_quot]

theorem quotient_inducedCF_formula_on_subgroup
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [A.Normal] [H.Normal] (hAH : A ≤ H)
    (theta : ClassFunction H)
    (thetaQuot : ClassFunction (quotientImageSubgroup H A))
    (hthetaQuot :
      ∀ h : H,
        thetaQuot ⟨((h : G) : G ⧸ A), quotientImageSubgroup_mk_mem H A h.2⟩ =
          theta h)
    (h : H) :
    inducedCF (quotientImageSubgroup H A) thetaQuot ((h : G) : G ⧸ A) =
      inducedCF H theta h := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (G ⧸ A) := Fintype.ofFinite (G ⧸ A)
  let B : Subgroup (G ⧸ A) := quotientImageSubgroup H A
  let hB : B := ⟨((h : G) : G ⧸ A), quotientImageSubgroup_mk_mem H A h.2⟩
  let F : G ⧸ A → ℂ := fun q =>
    thetaQuot ⟨q * ((h : G) : G ⧸ A) * q⁻¹,
      (show B.Normal from inferInstance).conj_mem hB.1 hB.2 q⟩
  have hterm : ∀ x : G,
      theta ⟨x * h.1 * x⁻¹, (show H.Normal from inferInstance).conj_mem h.1 h.2 x⟩ =
        F ((x : G ⧸ A)) := by
    intro x
    simpa [F, hB] using
      (hthetaQuot
        ⟨x * h.1 * x⁻¹, (show H.Normal from inferInstance).conj_mem h.1 h.2 x⟩).symm
  have hsumTheta :
      (∑ x : G, theta ⟨x * h.1 * x⁻¹,
        (show H.Normal from inferInstance).conj_mem h.1 h.2 x⟩) =
        ∑ x : G, F ((x : G ⧸ A)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact hterm x
  have hsumLift :
      (∑ x : G, theta ⟨x * h.1 * x⁻¹,
        (show H.Normal from inferInstance).conj_mem h.1 h.2 x⟩) =
        (Nat.card A : ℂ) * (∑ q : G ⧸ A, F q) := by
    rw [hsumTheta]
    exact quotient_sum_lift A F
  have hcard : Nat.card H = Nat.card B * Nat.card A := by
    simpa [B] using quotientImageSubgroup_card H A hAH
  have hA_ne : (Nat.card A : ℂ) ≠ 0 := by
    exact_mod_cast
      (Nat.card_ne_zero.mpr ⟨⟨1, A.one_mem⟩, inferInstance⟩ : Nat.card A ≠ 0)
  have hB_ne : (Nat.card B : ℂ) ≠ 0 := by
    exact_mod_cast
      (Nat.card_ne_zero.mpr ⟨⟨1, B.one_mem⟩, inferInstance⟩ : Nat.card B ≠ 0)
  calc
    inducedCF (quotientImageSubgroup H A) thetaQuot ((h : G) : G ⧸ A) =
        (Nat.card B : ℂ)⁻¹ * (∑ q : G ⧸ A, F q) := by
      rw [inducedCF, inducedClassFunction_formula_on_subgroup B thetaQuot hB]
    _ = (Nat.card H : ℂ)⁻¹ *
          ((Nat.card A : ℂ) * (∑ q : G ⧸ A, F q)) := by
      have hcardC : (Nat.card H : ℂ) = (Nat.card B : ℂ) * (Nat.card A : ℂ) := by
        exact_mod_cast hcard
      rw [hcardC]
      field_simp [hA_ne, hB_ne]
    _ = (Nat.card H : ℂ)⁻¹ *
          (∑ x : G, theta ⟨x * h.1 * x⁻¹,
            (show H.Normal from inferInstance).conj_mem h.1 h.2 x⟩) := by
      rw [hsumLift]
    _ = inducedCF H theta h := by
      rw [inducedCF, inducedClassFunction_formula_on_subgroup H theta h]

theorem subgroupInKernel'_character_of_subgroupInRepresentationKernel
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hV : subgroupInRepresentationKernel ρ A) :
    subgroupInKernel' ρ.character A := by
  intro a
  rw [degree]
  change LinearMap.trace ℂ V (ρ (a : G)) = LinearMap.trace ℂ V (ρ (1 : G))
  rw [hV a]
  simp

lemma complex_norm_eq_one_of_pow_eq_one {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) :
    ‖z‖ = 1 := by
  have hpow : ‖z‖ ^ n = (1 : ℝ) := by
    simpa [hz] using (norm_pow z n).symm
  have habs_pow : |(‖z‖ : ℝ) ^ n| = 1 := by
    rw [hpow, abs_one]
  have habs : |(‖z‖ : ℝ)| = 1 :=
    (abs_pow_eq_one (‖z‖ : ℝ) hn).mp habs_pow
  simpa [abs_of_nonneg (norm_nonneg z)] using habs

lemma complex_eq_one_of_pow_eq_one_of_one_le_re {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) (hre : 1 ≤ z.re) :
    z = 1 := by
  have hnorm : ‖z‖ = 1 := complex_norm_eq_one_of_pow_eq_one hn hz
  have hre_le : z.re ≤ 1 := by
    simpa [hnorm] using Complex.re_le_norm z
  have hre_eq : z.re = 1 := le_antisymm hre_le hre
  have hnormSq : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hnorm] at h
    norm_num at h
    exact h
  have him_sq : z.im * z.im = 0 := by
    nlinarith
  have him : z.im = 0 := mul_self_eq_zero.mp him_sq
  exact Complex.ext (by simp [hre_eq]) (by simp [him])

lemma eigenspace_finrank_pos
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (μ : f.Eigenvalues) :
    0 < Module.finrank ℂ (f.eigenspace (μ : ℂ)) := by
  have hμ : f.HasEigenvalue (μ : ℂ) :=
    Module.End.hasEigenvalue_of_hasGenEigenvalue μ.property
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨v, ?_⟩, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    exact hv.apply_eq_smul
  · intro hzero
    have hvzero : v = 0 := by
      simpa using congrArg Subtype.val hzero
    exact hv.2 hvzero

public theorem finite_order_eq_one_of_trace_eq_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1)
    (htrace : LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ)) :
    f = 1 := by
  classical
  let m : f.Eigenvalues → ℝ :=
    fun μ => (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℝ)
  have htrace_one :
      LinearMap.trace ℂ V f =
        ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) := by
    simpa [m] using
      (trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow)
  have htrace_zero :
      (Module.finrank ℂ V : ℂ) =
        ∑ μ : f.Eigenvalues, (m μ : ℂ) := by
    have h0 :=
      trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 0) hn hpow
    simpa [m, LinearMap.trace_id] using h0
  have hsum_complex :
      ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) =
        ∑ μ : f.Eigenvalues, (1 : ℂ) * (m μ : ℂ) := by
    rw [← htrace_one, htrace, htrace_zero]
    simp
  have hsum_real :
      ∑ μ : f.Eigenvalues, (μ : ℂ).re * m μ =
        ∑ μ : f.Eigenvalues, (1 : ℝ) * m μ := by
    have h := congrArg Complex.re hsum_complex
    simpa [Complex.re_sum, Complex.re_mul_ofReal] using h
  have hle :
      ∀ μ ∈ (Finset.univ : Finset f.Eigenvalues),
        (μ : ℂ).re * m μ ≤ (1 : ℝ) * m μ := by
    intro μ hμ
    have hμpow : (μ : ℂ) ^ n = 1 :=
      eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    have hnorm : ‖(μ : ℂ)‖ = 1 :=
      complex_norm_eq_one_of_pow_eq_one hn hμpow
    have hre_le : (μ : ℂ).re ≤ 1 := by
      simpa [hnorm] using Complex.re_le_norm (μ : ℂ)
    exact mul_le_mul_of_nonneg_right hre_le (by positivity : 0 ≤ m μ)
  have heq_each :
      ∀ μ : f.Eigenvalues, (μ : ℂ).re * m μ = (1 : ℝ) * m μ := by
    intro μ
    exact (Finset.sum_eq_sum_iff_of_le hle).mp (by simpa using hsum_real) μ
      (Finset.mem_univ μ)
  have heigen_eq_one : ∀ μ : f.Eigenvalues, (μ : ℂ) = 1 := by
    intro μ
    have hpos_nat : 0 < Module.finrank ℂ (f.eigenspace (μ : ℂ)) :=
      eigenspace_finrank_pos μ
    have hpos : 0 < m μ := by
      dsimp [m]
      exact_mod_cast hpos_nat
    have hre_eq : (μ : ℂ).re = 1 := by
      have h := heq_each μ
      nlinarith
    have hμpow : (μ : ℂ) ^ n = 1 :=
      eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    exact complex_eq_one_of_pow_eq_one_of_one_le_re hn hμpow (by linarith)
  have htop :
      f.eigenspace (1 : ℂ) = ⊤ := by
    have hsemi : f.IsSemisimple := end_isSemisimple_of_pow_eq_one f hn hpow
    have hiSup := eigenspace_iSup_eq_top_over_eigenvalues (f := f) hsemi
    apply top_unique
    rw [← hiSup]
    refine iSup_le ?_
    intro μ
    simp [heigen_eq_one μ]
  ext v
  have hv : v ∈ f.eigenspace (1 : ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hv
  simpa using hv

theorem subgroupInRepresentationKernel_of_subgroupInKernel'_character
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hV : subgroupInKernel' ρ.character A) :
    subgroupInRepresentationKernel ρ A := by
  intro a
  have hn : orderOf (a : G) ≠ 0 := Nat.ne_of_gt (orderOf_pos (a : G))
  have hpow : (ρ (a : G)) ^ orderOf (a : G) = 1 := by
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  have htrace : LinearMap.trace ℂ V (ρ (a : G)) = (Module.finrank ℂ V : ℂ) := by
    have hchar := hV a
    rw [degree] at hchar
    change ρ.character (a : G) = ρ.character (1 : G) at hchar
    simpa [Representation.character] using hchar
  have hρ : ρ (a : G) = 1 :=
    finite_order_eq_one_of_trace_eq_finrank (ρ (a : G)) hn hpow htrace
  exact hρ

public theorem subgroupInKernel'_character_iff_subgroupInRepresentationKernel
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) :
    subgroupInKernel' ρ.character A ↔ subgroupInRepresentationKernel ρ A := by
  constructor
  · exact subgroupInRepresentationKernel_of_subgroupInKernel'_character ρ A
  · exact subgroupInKernel'_character_of_subgroupInRepresentationKernel ρ A

lemma representation_character_eq_of_div_mem_kernel
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hker : subgroupInRepresentationKernel ρ A)
    {x y : G} (hxy : x / y ∈ A) :
    ρ.character x = ρ.character y := by
  let a : A := ⟨x / y, hxy⟩
  have hx : x = (a : G) * y := by
    simp [a, div_eq_mul_inv, mul_assoc]
  have hρ : ρ x = ρ y := by
    rw [hx, map_mul, hker a]
    simp
  simp [Representation.character, hρ]


lemma inducedCF_eq_of_div_mem_kernel
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (hker : subgroupInRepresentationKernel thetaRep (A.subgroupOf H))
    {g₁ g₂ : G} (hdiv : g₁ / g₂ ∈ A) :
    inducedCF H thetaRep.character g₁ = inducedCF H thetaRep.character g₂ := by
  classical
  unfold inducedCF inducedClassFunction
  refine congrArg ((Nat.card H : ℂ)⁻¹ * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro x _hx
  let d : G := x * (g₁ / g₂) * x⁻¹
  have hdA : d ∈ A := by
    dsimp [d]
    simpa using (show A.Normal from inferInstance).conj_mem (g₁ / g₂) hdiv x
  have hdH : d ∈ H := hAH hdA
  have hfactor : x * g₁ * x⁻¹ = d * (x * g₂ * x⁻¹) := by
    dsimp [d]
    rw [div_eq_mul_inv]
    group
  have hmem : x * g₁ * x⁻¹ ∈ H ↔ x * g₂ * x⁻¹ ∈ H := by
    constructor
    · intro hg₁
      have hdH_inv : d⁻¹ ∈ H := H.inv_mem hdH
      have hy : x * g₂ * x⁻¹ = d⁻¹ * (x * g₁ * x⁻¹) := by
        rw [hfactor]
        group
      rw [hy]
      exact H.mul_mem hdH_inv hg₁
    · intro hg₂
      rw [hfactor]
      exact H.mul_mem hdH hg₂
  by_cases hg₂ : x * g₂ * x⁻¹ ∈ H
  · have hg₁ : x * g₁ * x⁻¹ ∈ H := hmem.mpr hg₂
    have hdivH :
        (⟨x * g₁ * x⁻¹, hg₁⟩ / ⟨x * g₂ * x⁻¹, hg₂⟩ : H) ∈ A.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      change (x * g₁ * x⁻¹) / (x * g₂ * x⁻¹) ∈ A
      rw [hfactor]
      dsimp [d] at hdA ⊢
      simpa [div_eq_mul_inv, mul_assoc] using hdA
    have hchar :=
      representation_character_eq_of_div_mem_kernel thetaRep (A.subgroupOf H) hker hdivH
    simp [hg₁, hg₂, hchar]
  · have hg₁ : ¬ x * g₁ * x⁻¹ ∈ H := by
      intro hxg₁
      exact hg₂ (hmem.mp hxg₁)
    simp [hg₁, hg₂]

@[expose] public def conjugateOrbitSumRepresentation
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V) :
    Representation ℂ H (conjugateOrbitIndex H thetaRep.character → V) := by
  classical
  let ι := conjugateOrbitIndex H thetaRep.character
  letI : Fintype ι := Fintype.ofFinite ι
  exact
    { toFun := fun h =>
        { toFun := fun x i => (conjugateOrbitRepresentation H thetaRep i) h (x i)
          map_add' := by
            intro x y
            ext i
            simp
          map_smul' := by
            intro c x
            ext i
            simp }
      map_one' := by
        ext x i
        simp
      map_mul' := by
        intro a b
        ext x i
        simp [MonoidHom.map_mul] }

public theorem character_conjugateOrbitSumRepresentation
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V) :
    (conjugateOrbitSumRepresentation H thetaRep).character =
      fun h => ∑ i : conjugateOrbitIndex H thetaRep.character,
        conjugateOrbitConj H thetaRep.character i h := by
  classical
  funext h
  let ι := conjugateOrbitIndex H thetaRep.character
  letI : Fintype ι := Fintype.ofFinite ι
  let κ := Module.Free.ChooseBasisIndex ℂ V
  let b : Module.Basis κ ℂ V := Module.Free.chooseBasis ℂ V
  let L : ι → V →ₗ[ℂ] V :=
    fun i => (conjugateOrbitRepresentation H thetaRep i) h
  let T : (ι → V) →ₗ[ℂ] (ι → V) :=
    (conjugateOrbitSumRepresentation H thetaRep) h
  have htrace :
      LinearMap.trace ℂ (ι → V) T =
        ∑ i : ι, LinearMap.trace ℂ V (L i) := by
    have htrace_perm :=
      Theory.Representation.trace_pi_map_perm (R := ℂ) (ι := ι) (κ := κ) b
        (fun i : ι => i) L T (by
          intro x i
          rfl)
    simpa using htrace_perm
  calc
    (conjugateOrbitSumRepresentation H thetaRep).character h =
        LinearMap.trace ℂ (ι → V) T := by
          rfl
    _ = ∑ i : ι, LinearMap.trace ℂ V (L i) := htrace
    _ = ∑ i : ι, (conjugateOrbitRepresentation H thetaRep i).character h := by
          rfl
    _ = ∑ i : ι, conjugateOrbitConj H thetaRep.character i h := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [conjugateOrbitConj_representationCharacter H thetaRep i]

theorem subgroupInRepresentationKernel_conjugateOrbitSumRepresentation_component
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (A : Subgroup H) (i : conjugateOrbitIndex H thetaRep.character)
    (hker :
      subgroupInRepresentationKernel
        (conjugateOrbitSumRepresentation H thetaRep) A) :
    subgroupInRepresentationKernel (conjugateOrbitRepresentation H thetaRep i) A := by
  classical
  intro a
  let ι := conjugateOrbitIndex H thetaRep.character
  letI : Fintype ι := Fintype.ofFinite ι
  have hsum := hker a
  ext v
  let x : ι → V := fun j => if j = i then v else 0
  have heval :=
    congrArg
      (fun T : (ι → V) →ₗ[ℂ] (ι → V) => T x i) hsum
  change ((conjugateOrbitRepresentation H thetaRep i) (a : H)) (x i) = x i at heval
  simpa [x] using heval

lemma subgroupInKernel'_conjugateOnNormal
    {G : Type*} [Group G]
    (H A : Subgroup G) [hH : H.Normal] [hA : A.Normal] (hAH : A ≤ H)
    (theta : ClassFunction H)
    (hker : subgroupInKernel' theta (A.subgroupOf H)) (x : G) :
    subgroupInKernel' (conjugateOnNormal H theta x) (A.subgroupOf H) := by
  intro a
  have haA : (((a : A.subgroupOf H) : H) : G) ∈ A := by
    exact Subgroup.mem_subgroupOf.mp a.2
  have hxaA : x * (((a : A.subgroupOf H) : H) : G) * x⁻¹ ∈ A := by
    simpa using hA.conj_mem (((a : A.subgroupOf H) : H) : G) haA x
  have hxaH : x * (((a : A.subgroupOf H) : H) : G) * x⁻¹ ∈ H := hAH hxaA
  have hker' :
      theta ⟨x * (((a : A.subgroupOf H) : H) : G) * x⁻¹, hxaH⟩ =
        degree theta := by
    exact hker ⟨⟨x * (((a : A.subgroupOf H) : H) : G) * x⁻¹, hxaH⟩, by
      exact Subgroup.mem_subgroupOf.mpr hxaA⟩
  rw [degree_conjugateOnNormal H theta x]
  simpa [conjugateOnNormal] using hker'

lemma subgroupInKernel'_conjugateOrbitConj
    {G : Type*} [Group G]
    (H A : Subgroup G) [H.Normal] [A.Normal] (hAH : A ≤ H)
    (theta : ClassFunction H)
    (hker : subgroupInKernel' theta (A.subgroupOf H))
    (i : conjugateOrbitIndex H theta) :
    subgroupInKernel' (conjugateOrbitConj H theta i) (A.subgroupOf H) := by
  refine Quotient.inductionOn i ?_
  intro x
  exact subgroupInKernel'_conjugateOnNormal H A hAH theta hker x

private lemma eq_of_eqOn_subgroup_and_supportedOnSubgroup
    {G : Type*} [Group G]
    (H : Subgroup G) (phi psi : ClassFunction G)
    (hEq : subgroupRestriction H phi = subgroupRestriction H psi)
    (hphi : supportedOnSubgroup phi H)
    (hpsi : supportedOnSubgroup psi H) :
    phi = psi := by
  funext g
  by_cases hg : g ∈ H
  · exact congrArg (fun f => f ⟨g, hg⟩) hEq
  · rw [hphi g hg, hpsi g hg]

/-! ## Proposition (1.6): theorem-local nodes -/

lemma proposition_1_6_part_a_forward
    {G ι : Type*} [Group G] [Finite ι]
    (H A : Subgroup G) [Finite H] [A.Normal] (hAH : A ≤ H)
    (theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (r : ℕ) (chi : ClassFunction G)
    (hres : subgroupRestriction H chi = fun h => (r : ℂ) * ∑ i : ι, conjs i h)
    (hconjKernel :
      subgroupInKernel' theta (A.subgroupOf H) →
        ∀ i : ι, subgroupInKernel' (conjs i) (A.subgroupOf H)) :
    subgroupInKernel' theta (A.subgroupOf H) → subgroupInKernel' chi A := by
  intro htheta
  have hconjs : ∀ i : ι, subgroupInKernel' (conjs i) (A.subgroupOf H) :=
    hconjKernel htheta
  have hsum :
      subgroupInKernel' (fun h : H => ∑ i : ι, conjs i h) (A.subgroupOf H) :=
    subgroupInKernel'_fintype_sum conjs (A.subgroupOf H) hconjs
  have hscaled :
      subgroupInKernel' (fun h : H => (r : ℂ) * ∑ i : ι, conjs i h) (A.subgroupOf H) :=
    subgroupInKernel'_smul (r : ℂ) (fun h : H => ∑ i : ι, conjs i h) (A.subgroupOf H) hsum
  have hresKer : subgroupInKernel' (subgroupRestriction H chi) (A.subgroupOf H) :=
    subgroupInKernel'_of_eq hres.symm hscaled
  exact (subgroupInKernel'_subgroupRestriction_iff H A hAH chi).mp hresKer


lemma proposition_1_6_part_b
    {Q : Type*} [Group Q] (B : Subgroup Q)
    (chi indQ : ClassFunction Q)
    (hEq : subgroupRestriction B chi = subgroupRestriction B indQ)
    (hchi : supportedOnSubgroup chi B)
    (hindQ : supportedOnSubgroup indQ B) :
    chi = indQ := by
  exact eq_of_eqOn_subgroup_and_supportedOnSubgroup B chi indQ hEq hchi hindQ


theorem proposition_1_6_a_forward_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V) :
    subgroupInKernel' thetaRep.character (A.subgroupOf H) →
      subgroupInKernel' (inducedCF H thetaRep.character) A := by
  classical
  let theta : ClassFunction H := thetaRep.character
  letI : Fintype (conjugateOrbitIndex H theta) := Fintype.ofFinite _
  have hres :
      subgroupRestriction H (inducedCF H theta) =
        fun h =>
          (H.relIndex (inertiaSubgroup H theta) : ℂ) *
            ∑ i : conjugateOrbitIndex H theta, conjugateOrbitConj H theta i h := by
    dsimp [theta]
    exact proposition_1_5_a_orbit_relIndex_canonical H thetaRep
  have hconjKernel :
      subgroupInKernel' theta (A.subgroupOf H) →
        ∀ i : conjugateOrbitIndex H theta,
          subgroupInKernel' (conjugateOrbitConj H theta i) (A.subgroupOf H) := by
    intro htheta i
    exact subgroupInKernel'_conjugateOrbitConj H A hAH theta htheta i
  exact proposition_1_6_part_a_forward H A hAH theta
    (conjugateOrbitConj H theta)
    (H.relIndex (inertiaSubgroup H theta))
    (inducedCF H theta) hres hconjKernel

theorem proposition_1_6_a_reverse_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V) :
    subgroupInKernel' (inducedCF H thetaRep.character) A →
      subgroupInKernel' thetaRep.character (A.subgroupOf H) := by
  classical
  intro hind
  let theta : ClassFunction H := thetaRep.character
  let ι := conjugateOrbitIndex H theta
  let r : ℕ := H.relIndex (inertiaSubgroup H theta)
  letI : Fintype ι := Fintype.ofFinite ι
  let sumConj : ClassFunction H :=
    fun h => ∑ i : ι, conjugateOrbitConj H theta i h
  have hres :
      subgroupRestriction H (inducedCF H theta) =
        fun h =>
          (r : ℂ) *
            ∑ i : ι, conjugateOrbitConj H theta i h := by
    dsimp [theta, r]
    exact proposition_1_5_a_orbit_relIndex_canonical H thetaRep
  have hresKer :
      subgroupInKernel' (subgroupRestriction H (inducedCF H theta)) (A.subgroupOf H) :=
    (subgroupInKernel'_subgroupRestriction_iff H A hAH (inducedCF H theta)).mpr hind
  have hscaled :
      subgroupInKernel' ((r : ℂ) • sumConj) (A.subgroupOf H) := by
    change subgroupInKernel'
      (fun h : H => (r : ℂ) * ∑ i : ι, conjugateOrbitConj H theta i h)
      (A.subgroupOf H)
    exact subgroupInKernel'_of_eq hres hresKer
  have hr_ne : (r : ℂ) ≠ 0 := by
    exact_mod_cast (relIndex_inertia_ne_zero H theta)
  have hsumKer : subgroupInKernel' sumConj (A.subgroupOf H) :=
    subgroupInKernel'_of_smul_ne_zero hr_ne sumConj (A.subgroupOf H) hscaled
  have hsumKer' :
      subgroupInKernel'
        (fun h => ∑ i : conjugateOrbitIndex H thetaRep.character,
          conjugateOrbitConj H thetaRep.character i h)
        (A.subgroupOf H) := by
    simpa [sumConj, theta] using hsumKer
  have hsumRepCharKer :
      subgroupInKernel' (conjugateOrbitSumRepresentation H thetaRep).character
        (A.subgroupOf H) := by
    exact subgroupInKernel'_of_eq
      (character_conjugateOrbitSumRepresentation H thetaRep).symm hsumKer'
  have hsumRepKer :
      subgroupInRepresentationKernel
        (conjugateOrbitSumRepresentation H thetaRep) (A.subgroupOf H) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      (conjugateOrbitSumRepresentation H thetaRep) (A.subgroupOf H)).mp hsumRepCharKer
  let base : ι := conjugateOrbitFiber H theta 1
  have hbaseRepKer :
      subgroupInRepresentationKernel
        (conjugateOrbitRepresentation H thetaRep base) (A.subgroupOf H) :=
    subgroupInRepresentationKernel_conjugateOrbitSumRepresentation_component H thetaRep
      (A.subgroupOf H) base hsumRepKer
  have hbaseCharKer :
      subgroupInKernel' (conjugateOrbitRepresentation H thetaRep base).character
        (A.subgroupOf H) :=
    subgroupInKernel'_character_of_subgroupInRepresentationKernel
      (conjugateOrbitRepresentation H thetaRep base) (A.subgroupOf H) hbaseRepKer
  have hbaseConjKer :
      subgroupInKernel' (conjugateOrbitConj H theta base) (A.subgroupOf H) := by
    rw [conjugateOrbitConj_representationCharacter H thetaRep base]
    exact hbaseCharKer
  simpa [theta, base, conjugateOrbit_base_eq_theta H theta] using hbaseConjKer

public theorem proposition_1_6_a
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V) :
    subgroupInKernel' thetaRep.character (A.subgroupOf H) ↔
      subgroupInKernel' (inducedCF H thetaRep.character) A := by
  constructor
  · exact proposition_1_6_a_forward_canonical H A hAH thetaRep
  · exact proposition_1_6_a_reverse_canonical H A hAH thetaRep

theorem proposition_1_6_b_support_restriction
    {Q : Type*} [Group Q] (B : Subgroup Q)
    (chi indQ : ClassFunction Q)
    (hEq : subgroupRestriction B chi = subgroupRestriction B indQ)
    (hchi : supportedOnSubgroup chi B)
    (hindQ : supportedOnSubgroup indQ B) :
    chi = indQ :=
  proposition_1_6_part_b B chi indQ hEq hchi hindQ

theorem quotient_restriction_eq_of_induction_formula
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [A.Normal] [H.Normal]
    (theta : ClassFunction H)
    (thetaQuot : ClassFunction (quotientImageSubgroup H A))
    (chiQuot : ClassFunction (G ⧸ A))
    (hchiQuot :
      ∀ g : G, chiQuot (QuotientGroup.mk' A g) = inducedCF H theta g)
    (hindQuotFormula :
      ∀ h : H,
        inducedCF (quotientImageSubgroup H A) thetaQuot
          (QuotientGroup.mk' A (h : G)) =
            inducedCF H theta h) :
    subgroupRestriction (quotientImageSubgroup H A) chiQuot =
      subgroupRestriction (quotientImageSubgroup H A)
        (inducedCF (quotientImageSubgroup H A) thetaQuot) := by
  funext b
  rcases b.2 with ⟨g, hgH, hgq⟩
  let h : H := ⟨g, hgH⟩
  have hb :
      b = ⟨QuotientGroup.mk' A g, quotientImageSubgroup_mk_mem H A hgH⟩ := by
    ext
    exact hgq.symm
  calc
    subgroupRestriction (quotientImageSubgroup H A) chiQuot b =
        chiQuot (QuotientGroup.mk' A g) := by
          rw [hb]
          rfl
    _ = inducedCF H theta h := by
          simpa [h] using hchiQuot g
    _ = inducedCF (quotientImageSubgroup H A) thetaQuot (QuotientGroup.mk' A g) := by
          exact (hindQuotFormula h).symm
    _ = subgroupRestriction (quotientImageSubgroup H A)
          (inducedCF (quotientImageSubgroup H A) thetaQuot) b := by
          rw [hb]
          rfl

theorem proposition_1_6_b_from_quotient_formula
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [A.Normal] [H.Normal] (hAH : A ≤ H)
    (theta : ClassFunction H)
    (thetaQuot : ClassFunction (quotientImageSubgroup H A))
    (chiQuot : ClassFunction (G ⧸ A))
    (hchiQuot :
      ∀ g : G, chiQuot (QuotientGroup.mk' A g) = inducedCF H theta g)
    (hindQuotFormula :
      ∀ h : H,
        inducedCF (quotientImageSubgroup H A) thetaQuot
          (QuotientGroup.mk' A (h : G)) =
            inducedCF H theta h) :
    chiQuot = inducedCF (quotientImageSubgroup H A) thetaQuot := by
  apply proposition_1_6_b_support_restriction (quotientImageSubgroup H A)
  · exact quotient_restriction_eq_of_induction_formula H A theta
      thetaQuot chiQuot hchiQuot hindQuotFormula
  · exact quotient_lift_inducedCF_supported H A hAH theta chiQuot hchiQuot
  · exact quotient_inducedCF_supported H A thetaQuot

theorem proposition_1_6_b_conditional
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [A.Normal] [H.Normal] (hAH : A ≤ H)
    (theta : ClassFunction H)
    (thetaQuot : ClassFunction (quotientImageSubgroup H A))
    (chiQuot : ClassFunction (G ⧸ A))
    (_hthetaKernel : subgroupInKernel' theta (A.subgroupOf H))
    (hthetaQuot :
      ∀ h : H, ∀ hmem : ((h : G) : G ⧸ A) ∈ quotientImageSubgroup H A,
        thetaQuot ⟨((h : G) : G ⧸ A), hmem⟩ =
          theta h)
    (hchiQuot :
      ∀ g : G, chiQuot (QuotientGroup.mk' A g) = inducedCF H theta g) :
    chiQuot = inducedCF (quotientImageSubgroup H A) thetaQuot := by
  have hthetaQuot' :
      ∀ h : H,
        thetaQuot ⟨((h : G) : G ⧸ A), quotientImageSubgroup_mk_mem H A h.2⟩ =
          theta h := by
    intro h
    exact hthetaQuot h (quotientImageSubgroup_mk_mem H A h.2)
  exact proposition_1_6_b_from_quotient_formula H A hAH theta thetaQuot chiQuot
    hchiQuot (quotient_inducedCF_formula_on_subgroup H A hAH theta thetaQuot hthetaQuot')

public lemma quotientImageSubgroup_exists_preimage
    {G : Type*} [Group G] (H A : Subgroup G) [A.Normal]
    (q : quotientImageSubgroup H A) :
    ∃ h : H, QuotientGroup.mk' A (h : G) = q.1 := by
  rcases q.2 with ⟨g, hgH, hgq⟩
  exact ⟨⟨g, hgH⟩, hgq⟩

@[expose] public noncomputable def quotientThetaCharacter
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [A.Normal]
    (thetaRep : Representation ℂ H V) :
    ClassFunction (quotientImageSubgroup H A) :=
  fun q =>
    thetaRep.character
      (Classical.choose (quotientImageSubgroup_exists_preimage H A q))

public theorem quotientThetaCharacter_mk
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [A.Normal]
    (thetaRep : Representation ℂ H V)
    (hker : subgroupInRepresentationKernel thetaRep (A.subgroupOf H))
    (h : H) (hmem : ((h : G) : G ⧸ A) ∈ quotientImageSubgroup H A) :
    quotientThetaCharacter H A thetaRep ⟨((h : G) : G ⧸ A), hmem⟩ =
      thetaRep.character h := by
  classical
  let q : quotientImageSubgroup H A := ⟨((h : G) : G ⧸ A), hmem⟩
  let c : H := Classical.choose (quotientImageSubgroup_exists_preimage H A q)
  have hcq :
      QuotientGroup.mk' A (c : G) = q.1 :=
    Classical.choose_spec (quotientImageSubgroup_exists_preimage H A q)
  have hc : ((c : G) : G ⧸ A) = ((h : G) : G ⧸ A) := by
    simpa [q] using hcq
  have hdivA : (c : G) / (h : G) ∈ A :=
    (QuotientGroup.eq_iff_div_mem).mp hc
  have hdivH : (c / h : H) ∈ A.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hdivA
  change thetaRep.character c = thetaRep.character h
  exact representation_character_eq_of_div_mem_kernel thetaRep
    (A.subgroupOf H) hker hdivH

@[expose] public noncomputable def quotientInducedCF
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal]
    (theta : ClassFunction H) :
    ClassFunction (G ⧸ A) :=
  fun q => inducedCF H theta (Classical.choose (QuotientGroup.mk'_surjective A q))

public theorem quotientInducedCF_mk
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (hker : subgroupInRepresentationKernel thetaRep (A.subgroupOf H))
    (g : G) :
    quotientInducedCF H A thetaRep.character (QuotientGroup.mk' A g) =
      inducedCF H thetaRep.character g := by
  classical
  let x : G := Classical.choose
    (QuotientGroup.mk'_surjective A (QuotientGroup.mk' A g))
  have hx : QuotientGroup.mk' A x = QuotientGroup.mk' A g :=
    Classical.choose_spec
      (QuotientGroup.mk'_surjective A (QuotientGroup.mk' A g))
  have hdiv : x / g ∈ A := (QuotientGroup.eq_iff_div_mem).mp hx
  exact inducedCF_eq_of_div_mem_kernel H A hAH thetaRep hker hdiv

@[expose] public noncomputable def quotientRepresentationOfKernelSubgroup
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (hker : subgroupInRepresentationKernel ρ A) :
    Representation ℂ (G ⧸ A) V :=
  QuotientGroup.lift A ρ (by
    intro g hg
    rw [MonoidHom.mem_ker]
    exact hker ⟨g, hg⟩)

public theorem quotientRepresentationOfKernelSubgroup_mk
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (hker : subgroupInRepresentationKernel ρ A) (g : G) :
    quotientRepresentationOfKernelSubgroup ρ A hker (QuotientGroup.mk' A g) = ρ g := by
  exact QuotientGroup.lift_mk' (N := A)
    (φ := ρ) (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact hker ⟨x, hx⟩) g

@[expose] public noncomputable def quotientThetaRepresentation
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [A.Normal]
    (thetaRep : Representation ℂ H V)
    (hker : subgroupInRepresentationKernel thetaRep (A.subgroupOf H)) :
    Representation ℂ (quotientImageSubgroup H A) V :=
  (quotientRepresentationOfKernelSubgroup thetaRep (A.subgroupOf H) hker).comp
    (quotientSubgroupRangeEquiv H A).symm.toMonoidHom

public theorem quotientThetaRepresentation_character_mk
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [A.Normal]
    (thetaRep : Representation ℂ H V)
    (hker : subgroupInRepresentationKernel thetaRep (A.subgroupOf H))
    (h : H) (hmem : ((h : G) : G ⧸ A) ∈ quotientImageSubgroup H A) :
    (quotientThetaRepresentation H A thetaRep hker).character
        ⟨((h : G) : G ⧸ A), hmem⟩ =
      thetaRep.character h := by
  classical
  let q : quotientImageSubgroup H A := ⟨((h : G) : G ⧸ A), hmem⟩
  have hq :
      q = quotientSubgroupRangeEquiv H A
        (QuotientGroup.mk' (A.subgroupOf H) h) := by
    ext
    simpa [q] using (quotientSubgroupRangeEquiv_apply_mk H A h).symm
  have happ :
      quotientThetaRepresentation H A thetaRep hker q = thetaRep h := by
    change
      quotientRepresentationOfKernelSubgroup thetaRep (A.subgroupOf H) hker
        ((quotientSubgroupRangeEquiv H A).symm q) = thetaRep h
    rw [hq]
    simpa using
      quotientRepresentationOfKernelSubgroup_mk thetaRep (A.subgroupOf H) hker h
  simpa [Representation.character] using congrArg (LinearMap.trace ℂ V) happ

public theorem quotientThetaRepresentation_character
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [A.Normal]
    (thetaRep : Representation ℂ H V)
    (hker : subgroupInRepresentationKernel thetaRep (A.subgroupOf H)) :
    (quotientThetaRepresentation H A thetaRep hker).character =
      quotientThetaCharacter H A thetaRep := by
  classical
  funext q
  rcases quotientImageSubgroup_exists_preimage H A q with ⟨h, hq⟩
  have hq' : q = ⟨((h : G) : G ⧸ A), by
      simpa using quotientImageSubgroup_mk_mem H A h.2⟩ := by
    ext
    exact hq.symm
  rw [hq']
  calc
    (quotientThetaRepresentation H A thetaRep hker).character
        ⟨((h : G) : G ⧸ A), by simpa using quotientImageSubgroup_mk_mem H A h.2⟩ =
        thetaRep.character h := by
          exact quotientThetaRepresentation_character_mk H A thetaRep hker h
            (by simpa using quotientImageSubgroup_mk_mem H A h.2)
    _ = quotientThetaCharacter H A thetaRep
        ⟨((h : G) : G ⧸ A), by simpa using quotientImageSubgroup_mk_mem H A h.2⟩ := by
          exact (quotientThetaCharacter_mk H A thetaRep hker h
            (by simpa using quotientImageSubgroup_mk_mem H A h.2)).symm

public theorem inducedRepresentation_subgroupInRepresentationKernel
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (hthetaKernel : subgroupInKernel' thetaRep.character (A.subgroupOf H)) :
    subgroupInRepresentationKernel (Representation.ind H.subtype thetaRep) A := by
  have hindKernelCF :
      subgroupInKernel' (inducedCF H thetaRep.character) A :=
    (proposition_1_6_a H A hAH thetaRep).mp hthetaKernel
  have hindKernelChar :
      subgroupInKernel' (Representation.ind H.subtype thetaRep).character A :=
    subgroupInKernel'_of_eq
      (inducedCF_eq_representation_character_pf15 H thetaRep) hindKernelCF
  exact (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
    (Representation.ind H.subtype thetaRep) A).mp hindKernelChar

@[expose] public noncomputable def quotientInducedRepresentation
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (hthetaKernel : subgroupInKernel' thetaRep.character (A.subgroupOf H)) :
    Representation ℂ (G ⧸ A) (Representation.IndV H.subtype thetaRep) :=
  quotientRepresentationOfKernelSubgroup
    (Representation.ind H.subtype thetaRep) A
    (inducedRepresentation_subgroupInRepresentationKernel H A hAH thetaRep hthetaKernel)

public theorem quotientInducedRepresentation_mk
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (hthetaKernel : subgroupInKernel' thetaRep.character (A.subgroupOf H))
    (g : G) :
    quotientInducedRepresentation H A hAH thetaRep hthetaKernel (QuotientGroup.mk' A g) =
      (Representation.ind H.subtype thetaRep) g :=
  quotientRepresentationOfKernelSubgroup_mk
    (Representation.ind H.subtype thetaRep) A
    (inducedRepresentation_subgroupInRepresentationKernel H A hAH thetaRep hthetaKernel) g

public theorem quotientInducedRepresentation_character_mk
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (hthetaKernel : subgroupInKernel' thetaRep.character (A.subgroupOf H))
    (g : G) :
    (quotientInducedRepresentation H A hAH thetaRep hthetaKernel).character
        (QuotientGroup.mk' A g) =
      inducedCF H thetaRep.character g := by
  classical
  have happ :=
    quotientInducedRepresentation_mk H A hAH thetaRep hthetaKernel g
  simpa [Representation.character, inducedCF_eq_representation_character_pf15 H thetaRep]
    using congrArg (LinearMap.trace ℂ (Representation.IndV H.subtype thetaRep)) happ

public theorem quotientInducedRepresentation_character
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (hthetaKernel : subgroupInKernel' thetaRep.character (A.subgroupOf H)) :
    (quotientInducedRepresentation H A hAH thetaRep hthetaKernel).character =
      quotientInducedCF H A thetaRep.character := by
  classical
  funext q
  rcases QuotientGroup.mk'_surjective A q with ⟨g, rfl⟩
  rw [quotientInducedRepresentation_character_mk H A hAH thetaRep hthetaKernel g]
  exact (quotientInducedCF_mk H A hAH thetaRep
    ((subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      thetaRep (A.subgroupOf H)).mp hthetaKernel) g).symm

public theorem proposition_1_6_b_classFunction
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (hthetaKernel : subgroupInKernel' thetaRep.character (A.subgroupOf H)) :
    quotientInducedCF H A thetaRep.character =
      inducedCF (quotientImageSubgroup H A) (quotientThetaCharacter H A thetaRep) := by
  classical
  have hkerRep :
      subgroupInRepresentationKernel thetaRep (A.subgroupOf H) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      thetaRep (A.subgroupOf H)).mp hthetaKernel
  exact proposition_1_6_b_conditional H A hAH thetaRep.character
    (quotientThetaCharacter H A thetaRep)
    (quotientInducedCF H A thetaRep.character)
    hthetaKernel
    (by
      intro h hmem
      exact quotientThetaCharacter_mk H A thetaRep hkerRep h hmem)
    (by
      intro g
      exact quotientInducedCF_mk H A hAH thetaRep hkerRep g)

public theorem proposition_1_6_b
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A : Subgroup G) [Finite H] [H.Normal] [A.Normal] (hAH : A ≤ H)
    (thetaRep : Representation ℂ H V)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hthetaKernel : subgroupInKernel' thetaRep.character (A.subgroupOf H)) :
    (quotientInducedRepresentation H A hAH thetaRep hthetaKernel).character =
      (Representation.ind (quotientImageSubgroup H A).subtype
        (quotientThetaRepresentation H A thetaRep
          ((subgroupInKernel'_character_iff_subgroupInRepresentationKernel
            thetaRep (A.subgroupOf H)).mp hthetaKernel))).character := by
  classical
  have _hthetaIrr : Representation.IsIrreducible thetaRep := htheta_irreducible
  have hkerRep :
      subgroupInRepresentationKernel thetaRep (A.subgroupOf H) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      thetaRep (A.subgroupOf H)).mp hthetaKernel
  calc
    (quotientInducedRepresentation H A hAH thetaRep hthetaKernel).character =
        quotientInducedCF H A thetaRep.character := by
          exact quotientInducedRepresentation_character H A hAH thetaRep hthetaKernel
    _ = inducedCF (quotientImageSubgroup H A) (quotientThetaCharacter H A thetaRep) := by
          exact proposition_1_6_b_classFunction H A hAH thetaRep hthetaKernel
    _ =
        (Representation.ind (quotientImageSubgroup H A).subtype
          (quotientThetaRepresentation H A thetaRep hkerRep)).character := by
          rw [← quotientThetaRepresentation_character H A thetaRep hkerRep]
          exact inducedCF_eq_representation_character_pf15
            (quotientImageSubgroup H A)
            (quotientThetaRepresentation H A thetaRep hkerRep)

end CFSG.Section1
