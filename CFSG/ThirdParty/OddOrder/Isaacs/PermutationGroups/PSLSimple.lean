/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.TransvectionGeneration

/-!
# Isaacs, Finite Group Theory — Ch. 8: `PSL(n,q)` is simple (Thm 8.33)

Formalizes **Isaacs Thm 8.33** (pp. 241–242): the projective special linear
group over a field is simple when the dimension is at least `3`, or when the
field has a unit `β` with `β² ≠ 1` (for finite fields: `q > 3`)
(`isSimpleGroup_projectiveSpecialLinearGroup`).

Proof via the Iwasawa criterion (`MulAction.IwasawaStructure.isSimpleGroup`,
matching Isaacs's proof): `PSL` acts faithfully and (pre)primitively on the
projective space `ℙ K (ι → K)` (mathlib instances); to each line `[v]` we
attach the abelian *root subgroup*
`U_[v] = {A ∈ SL | ∃ φ, φ v = 0, A w = w + φ w • v}` of transvections with
center `[v]`; these are permuted by conjugation compatibly with the action,
and together they contain all transvections, hence generate `SL`
(Thm 8.31).  Since `SL` is perfect (Thm 8.32), so is `PSL`, and the Iwasawa
criterion applies.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open Matrix MulAction

open scoped MatrixGroups Pointwise LinearAlgebra.Projectivization

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

/-! ### Root subgroups of `SL` at a vector -/

section RootSubgroup

/-- Two special linear matrices acting identically on vectors are equal. -/
private lemma sl_ext_mulVec {A B : Matrix.SpecialLinearGroup ι K}
    (h : ∀ w : ι → K, (A : Matrix ι ι K) *ᵥ w = (B : Matrix ι ι K) *ᵥ w) :
    A = B := by
  apply Subtype.ext
  ext r s
  have h2 := congrFun (h (Pi.single s 1)) r
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
    Finset.sum_ite_eq', mul_comm] using h2

/-- The root subgroup at `v`: the transvections `w ↦ w + φ w • v` with
center along `v` (together with the identity). -/
private def rootSubgroup (v : ι → K) :
    Subgroup (Matrix.SpecialLinearGroup ι K) where
  carrier := {A | ∃ φ : (ι → K) →ₗ[K] K, φ v = 0 ∧
    ∀ w, (A : Matrix ι ι K) *ᵥ w = w + φ w • v}
  one_mem' := ⟨0, by simp, fun w => by simp⟩
  mul_mem' := by
    rintro A B ⟨φ, hφv, hφ⟩ ⟨ψ, hψv, hψ⟩
    refine ⟨φ + ψ, by simp [hφv, hψv], fun w => ?_⟩
    have hAv : (A : Matrix ι ι K) *ᵥ v = v := by
      rw [hφ v, hφv]
      simp
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hψ w,
      Matrix.mulVec_add, Matrix.mulVec_smul, hφ w, hAv,
      LinearMap.add_apply]
    module
  inv_mem' := by
    rintro A ⟨φ, hφv, hφ⟩
    refine ⟨-φ, by simp [hφv], fun w => ?_⟩
    have hAv : (A : Matrix ι ι K) *ᵥ v = v := by
      rw [hφ v, hφv]
      simp
    have key : (A : Matrix ι ι K) *ᵥ (w + (-φ) w • v) = w := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hφ w, hAv,
        LinearMap.neg_apply]
      module
    calc ((A⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) *ᵥ w
        = ((A⁻¹ * A : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) *ᵥ
            (w + (-φ) w • v) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, key]
      _ = w + (-φ) w • v := by
          rw [inv_mul_cancel]
          simp

private lemma mem_rootSubgroup_iff {v : ι → K}
    {A : Matrix.SpecialLinearGroup ι K} :
    A ∈ rootSubgroup v ↔ ∃ φ : (ι → K) →ₗ[K] K, φ v = 0 ∧
      ∀ w, (A : Matrix ι ι K) *ᵥ w = w + φ w • v :=
  Iff.rfl

/-- Root subgroups are commutative. -/
private lemma rootSubgroup_mul_comm {v : ι → K}
    {A B : Matrix.SpecialLinearGroup ι K}
    (hA : A ∈ rootSubgroup v) (hB : B ∈ rootSubgroup v) :
    A * B = B * A := by
  obtain ⟨φ, hφv, hφ⟩ := hA
  obtain ⟨ψ, hψv, hψ⟩ := hB
  have hAv : (A : Matrix ι ι K) *ᵥ v = v := by
    rw [hφ v, hφv]; simp
  have hBv : (B : Matrix ι ι K) *ᵥ v = v := by
    rw [hψ v, hψv]; simp
  apply sl_ext_mulVec
  intro w
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hψ w, hφ w,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, hφ w, hψ w, hAv, hBv]
  module

/-- Root subgroups only depend on the line spanned by `v`. -/
private lemma rootSubgroup_smul_eq {t : K} (ht : t ≠ 0) (v : ι → K) :
    rootSubgroup (t • v) = rootSubgroup v := by
  have key : ∀ (t : K), t ≠ 0 → ∀ v : ι → K,
      rootSubgroup v ≤ rootSubgroup (t • v) := by
    rintro t ht v A ⟨φ, hφv, hφ⟩
    refine ⟨t⁻¹ • φ, ?_, fun w => ?_⟩
    · rw [LinearMap.smul_apply, map_smul, hφv]
      simp
    · rw [hφ w, LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_comm t⁻¹,
        mul_assoc, inv_mul_cancel₀ ht, mul_one]
  refine le_antisymm ?_ (key t ht v)
  have h2 := key t⁻¹ (inv_ne_zero ht) (t • v)
  rwa [inv_smul_smul₀ ht] at h2

/-- Conjugation carries the root subgroup at `v` to the root subgroup at
`g *ᵥ v`. -/
private lemma conj_mem_rootSubgroup {v : ι → K}
    {B : Matrix.SpecialLinearGroup ι K} (hB : B ∈ rootSubgroup v)
    (g : Matrix.SpecialLinearGroup ι K) :
    g * B * g⁻¹ ∈ rootSubgroup ((g : Matrix ι ι K) *ᵥ v) := by
  obtain ⟨φ, hφv, hφ⟩ := hB
  have hgg : ∀ u : ι → K,
      (g : Matrix ι ι K) *ᵥ (((g⁻¹ : Matrix.SpecialLinearGroup ι K) :
        Matrix ι ι K) *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hgg' : ∀ u : ι → K,
      ((g⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) *ᵥ
        ((g : Matrix ι ι K) *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  refine ⟨φ.comp (Matrix.mulVecLin
    ((g⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K)), ?_, fun w => ?_⟩
  · simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
    rw [hgg' v, hφv]
  · simp only [Matrix.SpecialLinearGroup.coe_mul, LinearMap.comp_apply,
      Matrix.mulVecLin_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hφ (((g⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) *ᵥ w),
      Matrix.mulVec_add, Matrix.mulVec_smul, hgg w]

/-- Conjugation equivariance of the root subgroups. -/
private lemma rootSubgroup_conj (g : Matrix.SpecialLinearGroup ι K)
    (v : ι → K) :
    MulAut.conj g • rootSubgroup v =
      rootSubgroup ((g : Matrix ι ι K) *ᵥ v) := by
  apply le_antisymm
  · intro A hA
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hA
    have h2 := conj_mem_rootSubgroup hA g
    have h3 : g * ((MulAut.conj g)⁻¹ • A) * g⁻¹ = A := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
      group
    rwa [h3] at h2
  · intro A hA
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h2 := conj_mem_rootSubgroup hA g⁻¹
    have h3 : ((g⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) *ᵥ
        ((g : Matrix ι ι K) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [h3, inv_inv] at h2
    have h4 : (MulAut.conj g)⁻¹ • A = g⁻¹ * A * g := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
    rwa [h4]

/-- Transvections `tᵢⱼ(c)` lie in the root subgroup at the basis vector
`eᵢ`. -/
private lemma mem_rootSubgroup_single {i j : ι} (hij : i ≠ j) (c : K)
    {t : Matrix.SpecialLinearGroup ι K}
    (ht : (t : Matrix ι ι K) = Matrix.transvection i j c) :
    t ∈ rootSubgroup (Pi.single i 1) := by
  refine ⟨c • LinearMap.proj j, ?_, fun w => ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.proj_apply,
      Pi.single_eq_of_ne hij.symm]
    exact smul_zero c
  · rw [ht, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec]
    congr 1
    ext r
    simp only [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      Function.update_apply, Pi.zero_apply, Pi.smul_apply, Pi.single_apply]
    by_cases hr : r = i <;> simp [hr]

end RootSubgroup

/-! ### The Iwasawa structure on the projective space -/

section Iwasawa

open scoped MatrixGroups

variable (ι K) in
/-- The Iwasawa root subgroups on the projective space: at a line `[v]`, the
image in `PSL` of the root subgroup at `v`. -/
private def rootT : ℙ K (ι → K) →
    Subgroup (Matrix.ProjectiveSpecialLinearGroup ι K) :=
  Projectivization.lift
    (fun v => (rootSubgroup v.1).map
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι K))))
    (by
      intro a b t hab
      have h2 : (a : ι → K) = t • (b : ι → K) := hab
      have ht : t ≠ 0 := by
        rintro rfl
        rw [zero_smul] at h2
        exact a.2 h2
      simp only [h2, rootSubgroup_smul_eq ht])

private lemma rootT_mk {v : ι → K} (hv : v ≠ 0) :
    rootT ι K (Projectivization.mk K v hv) =
      (rootSubgroup v).map
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι K))) :=
  rfl

/-- Mapping a subgroup through a homomorphism commutes with conjugation. -/
private lemma map_conj_smul {G H : Type*} [Group G] [Group H] (f : G →* H)
    (g : G) (S : Subgroup G) :
    (MulAut.conj g • S).map f = MulAut.conj (f g) • S.map f := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨g⁻¹ * a * g, ha, ?_⟩
    simp only [map_mul, map_inv]
  · rintro ⟨b, hb, hbx⟩
    refine ⟨g * b * g⁻¹, ?_, ?_⟩
    · have h2 : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      rwa [h2]
    · have hx : x = f g * f b * (f g)⁻¹ := by
        rw [hbx]
        group
      rw [hx]
      simp only [map_mul, map_inv]

private lemma sl_smul_projMk (g : Matrix.SpecialLinearGroup ι K) {v : ι → K}
    (hv : v ≠ 0) :
    g • Projectivization.mk K v hv =
      Projectivization.mk K ((g : Matrix ι ι K) *ᵥ v)
        (by
          intro h0
          have := congrArg (fun w =>
            ((g⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) *ᵥ w) h0
          simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
            inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
            Matrix.one_mulVec, Matrix.mulVec_zero] at this
          exact hv this) :=
  rfl

variable (ι K) in
/-- The Iwasawa structure of the root subgroups on the projective space. -/
private def pslIwasawaStructure :
    IwasawaStructure (Matrix.ProjectiveSpecialLinearGroup ι K)
      (ℙ K (ι → K)) where
  T := rootT ι K
  is_comm := by
    intro x
    induction x using Projectivization.ind with
    | h v hv =>
      rw [rootT_mk hv]
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨A, hA, hAa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨B, hB, hBb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hAa, ← hBb, ← map_mul,
        ← map_mul, rootSubgroup_mul_comm hA hB]
  is_conj := by
    intro g x
    induction x using Projectivization.ind with
    | h v hv =>
      induction g using QuotientGroup.induction_on with
      | H g' =>
        have h1 : (QuotientGroup.mk g' :
            Matrix.ProjectiveSpecialLinearGroup ι K) •
            Projectivization.mk K v hv =
            g' • Projectivization.mk K v hv := rfl
        rw [h1, sl_smul_projMk g' hv, rootT_mk, rootT_mk hv,
          ← rootSubgroup_conj, map_conj_smul]
        rfl
  is_generator := by
    rw [eq_top_iff]
    have h1 : (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup ι K)) =
        Subgroup.map (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup ι K))) ⊤ :=
      (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)).symm
    rw [h1, ← closure_transvections_eq_top (n := ι) (𝕜 := K),
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨t, ⟨i, j, hij, c, hc⟩, rfl⟩
    have hne : (Pi.single i 1 : ι → K) ≠ 0 := by
      intro h0
      have h2 := congrFun h0 i
      simp at h2
    have hmem : QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup ι K)) t ∈
        rootT ι K (Projectivization.mk K (Pi.single i 1) hne) := by
      rw [rootT_mk hne]
      exact Subgroup.mem_map.mpr ⟨t, mem_rootSubgroup_single hij c hc, rfl⟩
    exact SetLike.mem_coe.mpr (Subgroup.mem_iSup_of_mem _ hmem)

set_option backward.isDefEq.respectTransparency false in
/-- `PSL` is nontrivial: the class of a transvection is not the identity. -/
private lemma nontrivial_psl [Nontrivial ι] :
    Nontrivial (Matrix.ProjectiveSpecialLinearGroup ι K) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  refine ⟨QuotientGroup.mk ⟨Matrix.transvection i j 1,
    det_transvection_of_ne i j hij 1⟩, 1, ?_⟩
  rw [Ne, QuotientGroup.eq_one_iff]
  intro hmem
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  have h2 := congrFun (congrFun hr i) j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h2
  have h3 : (Matrix.transvection i j (1 : K)) i j = 1 := by
    simp [Matrix.transvection, hij]
  exact zero_ne_one (h2.trans h3)

/-- `PSL` is perfect (as the quotient of the perfect group `SL`). -/
private lemma commutator_psl_eq_top
    (h : 3 ≤ Nat.card ι ∨ ∃ β : K, β ≠ 0 ∧ β ^ 2 ≠ 1) :
    commutator (Matrix.ProjectiveSpecialLinearGroup ι K) = ⊤ := by
  have h1 := commutator_specialLinearGroup_eq_top (n := ι) (𝕜 := K) h
  have hsurj := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup ι K))
  calc commutator (Matrix.ProjectiveSpecialLinearGroup ι K)
      = ⁅(⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup ι K)), ⊤⁆ :=
        commutator_def _
    _ = ⁅Subgroup.map (QuotientGroup.mk' _) ⊤,
          Subgroup.map (QuotientGroup.mk' _) ⊤⁆ := by
        rw [Subgroup.map_top_of_surjective _ hsurj]
    _ = Subgroup.map (QuotientGroup.mk' _) ⁅⊤, ⊤⁆ :=
        (Subgroup.map_commutator _ _ _).symm
    _ = Subgroup.map (QuotientGroup.mk' _)
          (commutator (Matrix.SpecialLinearGroup ι K)) := by
        rw [commutator_def]
    _ = Subgroup.map (QuotientGroup.mk' _) ⊤ := by rw [h1]
    _ = ⊤ := Subgroup.map_top_of_surjective _ hsurj

/-- **Isaacs Thm 8.33** — `PSL(n, 𝕜)` is simple when the index type has at
least two elements and either it has at least three elements or the field
contains a unit `β` with `β² ≠ 1` (for a finite field of order `q`, the
latter is exactly `q > 3`; the book states the result for `n ≥ 3` or
`n = 2, q > 3`). -/
theorem isSimpleGroup_projectiveSpecialLinearGroup [Nontrivial ι]
    (h : 3 ≤ Nat.card ι ∨ ∃ β : K, β ≠ 0 ∧ β ^ 2 ≠ 1) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup ι K) := by
  have := nontrivial_psl (ι := ι) (K := K)
  exact (pslIwasawaStructure ι K).isSimpleGroup (commutator_psl_eq_top h)
    inferInstance

end Iwasawa

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
