module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerScalar
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.Finite.Basic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module

theorem sum_filter_eq_zero_of_eigen {R M : Type*} [Field R] [DecidableEq R] [AddCommGroup M]
    [Module R M] (f : Module.End R M) {ι : Type*} (s : Finset ι) (v : ι → M) (μ : ι → R)
    (hv : ∀ i ∈ s, f (v i) = μ i • v i) (hsum : ∑ i ∈ s, v i = 0) (ν : R) :
    ∑ i ∈ s with μ i = ν, v i = 0 := by
  have hA : ∑ i ∈ s with μ i = ν, v i ∈ f.eigenspace ν := by
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [Module.End.mem_eigenspace_iff, ← hi.2]
    exact hv i hi.1
  have hB : ∑ i ∈ s with ¬ μ i = ν, v i ∈ ⨆ j, ⨆ (_ : j ≠ ν), f.eigenspace j := by
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_filter] at hi
    have hmem : v i ∈ f.eigenspace (μ i) := Module.End.mem_eigenspace_iff.mpr (hv i hi.1)
    exact (le_iSup₂ (f := fun j (_ : j ≠ ν) => f.eigenspace j) (μ i) hi.2) hmem
  have hAB := Finset.sum_filter_add_sum_filter_not s (fun i => μ i = ν) v
  rw [hsum] at hAB
  have hneg : ∑ i ∈ s with μ i = ν, v i = -∑ i ∈ s with ¬ μ i = ν, v i :=
    eq_neg_of_add_eq_zero_left hAB
  have hB' : ∑ i ∈ s with μ i = ν, v i ∈ ⨆ j, ⨆ (_ : j ≠ ν), f.eigenspace j := by
    rw [hneg]
    exact Submodule.neg_mem _ hB
  exact (Module.End.eigenspaces_iSupIndep f ν).le_bot ⟨hA, hB'⟩

theorem mem_range_of_sq_mem {k F : Type*} [Field k] [Field F] [Algebra k F] [Finite F]
    [CharP F 2] {b : F} (hb : b ^ 2 ∈ Set.range (algebraMap k F)) :
    b ∈ Set.range (algebraMap k F) := by
  have : Fintype F := Fintype.ofFinite F
  by_cases hb0 : b = 0
  · exact ⟨0, by rw [hb0, map_zero]⟩
  have hodd : Odd (Fintype.card F - 1) := by
    have h2 : 2 ∣ Fintype.card F := (CharP.cast_eq_zero_iff F 2 _).mp (FiniteField.cast_card_eq_zero F)
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  obtain ⟨j, hj⟩ := hodd
  have hpow : b = (b ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, ← hj,
      FiniteField.pow_card_sub_one_eq_one b hb0, one_mul]
  rw [hpow]
  have hsub : Set.range (algebraMap k F) = ((algebraMap k F).fieldRange : Set F) := by
    ext x
    simp
  rw [hsub] at hb ⊢
  exact Subfield.pow_mem _ hb _

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem exists_eq_smul_of_forall_smul_eq [Finite F] [CharP F 2] {Δ : Set (ℙ k F)}
    (hspan : ⨆ p ∈ Δ, p.submodule = ⊤) {B : Subgroup Fˣ} (hBΔ : ∀ b ∈ B, ∀ p ∈ Δ, b • p ∈ Δ)
    {d : F ≃ₗ[k] F} (hd : ∀ p ∈ Δ, d • p = p) (hdB : ∀ q : ℙ k F, ∃ b ∈ B, d • q = b • q) :
    ∃ c : k, ∀ x, d x = c • x := by
  classical
  have hd0 : ∀ {v : F}, v ≠ 0 → d v ≠ 0 := fun hv h => hv (d.injective (h.trans d.map_zero.symm))
  have heig : ∀ {v : F} (hv : v ≠ 0), Projectivization.mk k v hv ∈ Δ → ∃ α : k, d v = α • v := by
    intro v hv hvΔ
    have h := hd _ hvΔ
    rw [smul_mk, mk_eq_mk_iff'] at h
    obtain ⟨α, hα⟩ := h
    exact ⟨α, hα.symm⟩
  have huniq : ∀ {v : F}, v ≠ 0 → ∀ {α β : k}, d v = α • v → d v = β • v → α = β := by
    intro v hv α β hα hβ
    exact smul_left_injective k hv (hα.symm.trans hβ)
  have hsame : ∀ {x y : F} (hx : x ≠ 0) (hy : y ≠ 0), Projectivization.mk k x hx ∈ Δ →
      Projectivization.mk k y hy ∈ Δ → ∀ {α β : k}, d x = α • x → d y = β • y → α = β := by
    intro x y hx hy hxΔ hyΔ α β hα hβ
    by_contra hne
    have hα0 : α ≠ 0 := by
      rintro rfl
      exact hd0 hx (by rw [hα, zero_smul])
    have hβ0 : β ≠ 0 := by
      rintro rfl
      exact hd0 hy (by rw [hβ, zero_smul])
    have hxy : x + y ≠ 0 := by
      intro h
      have hyx : y = -x := eq_neg_of_add_eq_zero_right h
      apply hne
      refine huniq hy ?_ hβ
      rw [hyx, map_neg, hα, smul_neg]
    obtain ⟨b, hb, hbq⟩ := hdB (Projectivization.mk k (x + y) hxy)
    rw [smul_mk, units_smul_mk, mk_eq_mk_iff'] at hbq
    obtain ⟨μ, hμ⟩ := hbq
    rw [LinearEquiv.smul_def, map_add, hα, hβ] at hμ
    have hbx0 : (b : F) * x ≠ 0 := mul_ne_zero b.ne_zero hx
    have hby0 : (b : F) * y ≠ 0 := mul_ne_zero b.ne_zero hy
    obtain ⟨α', hα'⟩ := heig hbx0 (hBΔ b hb _ hxΔ :)
    obtain ⟨β', hβ'⟩ := heig hby0 (hBΔ b hb _ hyΔ :)
    set f : Module.End k F := (d : F →ₗ[k] F)
    have hsum := sum_filter_eq_zero_of_eigen f Finset.univ
      ![α • x, β • y, -(μ • ((b : F) * x)), -(μ • ((b : F) * y))] ![α, β, α', β']
      (by
        intro i _
        fin_cases i
        · show f (α • x) = α • (α • x)
          simp only [f, LinearEquiv.coe_coe, map_smul, hα]
        · show f (β • y) = β • (β • y)
          simp only [f, LinearEquiv.coe_coe, map_smul, hβ]
        · show f (-(μ • ((b : F) * x))) = α' • -(μ • ((b : F) * x))
          simp only [f, LinearEquiv.coe_coe, map_neg, map_smul, hα', smul_neg, smul_comm α' μ]
        · show f (-(μ • ((b : F) * y))) = β' • -(μ • ((b : F) * y))
          simp only [f, LinearEquiv.coe_coe, map_neg, map_smul, hβ', smul_neg, smul_comm β' μ])
      (by
        rw [Fin.sum_univ_four]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        rw [← hμ, mul_add, smul_add]
        abel)
    have hne' : β ≠ α := Ne.symm hne
    have hαx : α • x ≠ 0 := smul_ne_zero hα0 hx
    have hβy : β • y ≠ 0 := smul_ne_zero hβ0 hy
    have gα := hsum α
    have gβ := hsum β
    simp only [Finset.sum_filter, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hne, hne',
      ↓reduceIte, add_zero, zero_add] at gα gβ
    by_cases h1 : α' = α
    · by_cases h2 : β' = β
      ·
        simp only [h1, h2, hne, hne', ↓reduceIte, add_zero] at gα gβ
        rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← sub_eq_add_neg, ← sub_mul] at gα gβ
        have e1 := (mul_eq_zero.mp gα).resolve_right hx
        have e2 := (mul_eq_zero.mp gβ).resolve_right hy
        exact hne ((algebraMap k F).injective (by linear_combination e1 - e2))
      · simp only [h1, h2, hne, ↓reduceIte, add_zero] at gβ
        exact hβy gβ
    by_cases h2 : β' = α
    swap
    · simp only [h1, h2, ↓reduceIte, add_zero] at gα
      exact hαx gα
    by_cases h3 : α' = β
    swap
    · simp only [h2, h3, hne, ↓reduceIte, add_zero] at gβ
      exact hβy gβ
    simp only [h2, h3, hne, hne', ↓reduceIte, add_zero] at gα gβ
    rw [Algebra.smul_def, Algebra.smul_def] at gα gβ
    have e1 : algebraMap k F α * x = algebraMap k F μ * b * y := by linear_combination gα
    have e2 : algebraMap k F β * y = algebraMap k F μ * b * x := by linear_combination gβ
    have hμ0 : algebraMap k F μ ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_mul] at e1
      exact hαx (by rw [Algebra.smul_def, e1])
    have hsq : (b : F) ^ 2 = algebraMap k F (α * β * (μ ^ 2)⁻¹) := by
      have e3 : algebraMap k F α * algebraMap k F β * (x * y) =
          (algebraMap k F μ) ^ 2 * (b : F) ^ 2 * (x * y) := by
        linear_combination (algebraMap k F β * y) * e1 + (algebraMap k F μ * b * y) * e2
      have e4 := mul_right_cancel₀ (mul_ne_zero hx hy) e3
      rw [map_mul, map_mul, map_inv₀, map_pow, e4]
      field_simp
    obtain ⟨c, hc⟩ := mem_range_of_sq_mem (k := k) ⟨_, hsq.symm⟩
    apply h1
    refine huniq hbx0 hα' ?_
    rw [← hc, ← Algebra.smul_def, map_smul, hα, smul_comm]
  obtain ⟨p₀, hp₀⟩ : Δ.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot] at hspan
    exact bot_ne_top hspan
  have hp₀' : Projectivization.mk k p₀.rep p₀.rep_nonzero ∈ Δ := by rwa [mk_rep]
  obtain ⟨c, hc⟩ := heig p₀.rep_nonzero hp₀'
  refine ⟨c, fun x => ?_⟩
  have hW : x ∈ ⨆ p ∈ Δ, p.submodule := hspan ▸ Submodule.mem_top
  have hle : (⨆ p ∈ Δ, p.submodule) ≤ LinearMap.ker ((d : F →ₗ[k] F) - c • LinearMap.id) := by
    refine iSup₂_le fun p hp => ?_
    rw [submodule_eq, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hp' : Projectivization.mk k p.rep p.rep_nonzero ∈ Δ := by rwa [mk_rep]
    obtain ⟨α, hα⟩ := heig p.rep_nonzero hp'
    rw [LinearEquiv.coe_coe, hα, hsame p.rep_nonzero p₀.rep_nonzero hp' hp₀' hα hc]
  have := hle hW
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at this
  exact this

end CFSG.ShultStronglyClosedTI.Singer
