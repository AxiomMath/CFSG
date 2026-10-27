module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

public section

namespace CFSG.StandardType.E6QTwo

open Module

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] def cartanE6ModThree : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.of fun i j => ((CartanMatrix.E 6) i j : ZMod 3)

@[expose] def cartanE6KernelVec : Fin 6 → ZMod 3 := ![1, 0, 2, 0, 1, 2]

theorem cartanE6ModThree_symm (i j : Fin 6) :
    cartanE6ModThree i j = cartanE6ModThree j i := by
  have h := Matrix.IsSymm.apply (CartanMatrix.E_isSymm 6) i j
  simp [cartanE6ModThree, h]

theorem cartanE6KernelVec_ne_zero : cartanE6KernelVec ≠ 0 := by
  decide +kernel

theorem cartanE6ModThree_mulVec_cartanE6KernelVec :
    cartanE6ModThree *ᵥ cartanE6KernelVec = 0 := by
  decide +kernel

theorem cartanE6KernelVec_mulVec_transpose (k : Fin 6) :
    ∑ j, cartanE6KernelVec j * (CartanMatrix.E 6 j k : ZMod 3) = 0 := by
  revert k
  decide +kernel

theorem eq_smul_cartanE6KernelVec :
    ∀ c : Fin 6 → ZMod 3, cartanE6ModThree *ᵥ c = 0 → c = c 0 • cartanE6KernelVec := by
  decide +kernel

theorem apply_linearCombination_eq_cartanE6ModThree {h : Fin 6 → V}
    {α : Fin 6 → Dual (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) (i : Fin 6)
    (c : Fin 6 → ZMod 3) :
    α i (Fintype.linearCombination (ZMod 3) h c) = (cartanE6ModThree *ᵥ c) i := by
  rw [Fintype.linearCombination_apply, map_sum]
  simp only [map_smul, Matrix.mulVec, dotProduct, cartanE6ModThree, Matrix.of_apply, smul_eq_mul,
    hP]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem five_le_finrank_span {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    5 ≤ finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) := by
  have hdet : (Matrix.of fun i j : Fin 5 => α i.succ (h j.succ)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j : Fin 5 => α i.succ (h j.succ))
        = Matrix.of fun i j : Fin 5 => ((CartanMatrix.E 6) i.succ j.succ : ZMod 3) := by
      ext i j
      exact hP i.succ j.succ
    rw [hmat]
    decide +kernel
  have hli : LinearIndependent (ZMod 3) (fun k : Fin 5 => h k.succ) :=
    linearIndependent_of_det_ne_zero (fun k : Fin 5 => h k.succ) (fun k => α k.succ) hdet
  have hfin : finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range fun k : Fin 5 => h k.succ)) = 5 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  haveI : Module.Finite (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range h))
  have hle : Submodule.span (ZMod 3) (Set.range fun k : Fin 5 => h k.succ) ≤
      Submodule.span (ZMod 3) (Set.range h) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k.succ, rfl⟩
  have hmono := Submodule.finrank_mono hle
  omega

theorem linearCombination_radical_eq_zero_of_dependent
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) h) :
    Fintype.linearCombination (ZMod 3) h cartanE6KernelVec = 0 := by
  classical
  obtain ⟨c, hc, hcne⟩ : ∃ c : Fin 6 → ZMod 3, (∑ j, c j • h j) = 0 ∧ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hdep (Fintype.linearIndependent_iff.mpr fun g hg => by
      have h0 : g = 0 := hcon g hg
      intro i
      rw [h0]
      rfl)
  have hcE : Fintype.linearCombination (ZMod 3) h c = 0 := hc
  have hcC : cartanE6ModThree *ᵥ c = 0 := by
    ext i
    have h' := congrArg (α i) hcE
    simp only [map_zero] at h'
    rwa [apply_linearCombination_eq_cartanE6ModThree hpair i c] at h'
  have hcn : c = c 0 • cartanE6KernelVec := eq_smul_cartanE6KernelVec c hcC
  have hc0 : c 0 ≠ 0 := by
    intro h0
    have hzero : c = 0 := by rw [hcn, h0, zero_smul]
    exact hcne hzero
  have hct : (c 0) • (Fintype.linearCombination (ZMod 3) h cartanE6KernelVec) =
      Fintype.linearCombination (ZMod 3) h c := by
    conv_rhs => rw [hcn]
    rw [map_smul]
  have h0 : (c 0) • (Fintype.linearCombination (ZMod 3) h cartanE6KernelVec) = 0 := by
    rw [hct, hcE]
  exact (smul_eq_zero.mp h0).resolve_left hc0

theorem eq_zero_of_mem_coroot_span_of_dependent
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) h) {v : V}
    (hv : v ∈ Submodule.span (ZMod 3) (Set.range h))
    (hvfix : ∀ i, α i v = 0) : v = 0 := by
  classical
  rw [← Fintype.range_linearCombination] at hv
  obtain ⟨c, rfl⟩ := hv
  have hcC : cartanE6ModThree *ᵥ c = 0 := by
    ext i
    have h' := hvfix i
    rwa [apply_linearCombination_eq_cartanE6ModThree hpair i c] at h'
  rw [eq_smul_cartanE6KernelVec c hcC, map_smul,
    linearCombination_radical_eq_zero_of_dependent h α hpair hdep, smul_zero]

variable [Finite V] {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}

theorem finrank_eq_five (hV : Nat.card V = 3 ^ 5) : finrank (ZMod 3) V = 5 := by
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
  rw [Nat.card_zmod, hV] at hcard
  exact (Nat.pow_right_injective (by norm_num) hcard).symm

theorem span_eq_top_of_card (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) : Submodule.span (ZMod 3) (Set.range h) = ⊤ := by
  have hfin : finrank (ZMod 3) V = 5 := finrank_eq_five hV
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hfin]
  refine le_antisymm ?_ (five_le_finrank_span hP)
  simpa [hfin] using
    Submodule.finrank_le (Submodule.span (ZMod 3) (Set.range h))

theorem linearCombination_cartanE6KernelVec_eq_zero
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) :
    Fintype.linearCombination (ZMod 3) h cartanE6KernelVec = 0 := by
  have hfin : finrank (ZMod 3) V = 5 := finrank_eq_five hV
  have hnotli : ¬ LinearIndependent (ZMod 3) h := by
    intro hli
    have hle := hli.fintype_card_le_finrank (M := V)
    rw [Fintype.card_fin, hfin] at hle
    omega
  exact linearCombination_radical_eq_zero_of_dependent h α hP hnotli

theorem eq_zero_of_forall_apply_eq_zero (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) {v : V} (hv : ∀ i, α i v = 0) : v = 0 := by
  have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ := span_eq_top_of_card hP hV
  have hsurj : Function.Surjective (Fintype.linearCombination (ZMod 3) h) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  have hEn : Fintype.linearCombination (ZMod 3) h cartanE6KernelVec = 0 :=
    linearCombination_cartanE6KernelVec_eq_zero hP hV
  obtain ⟨c, rfl⟩ := hsurj v
  have hcC : cartanE6ModThree *ᵥ c = 0 := by
    ext i
    have h' := hv i
    rwa [apply_linearCombination_eq_cartanE6ModThree hP i c] at h'
  rw [eq_smul_cartanE6KernelVec c hcC, map_smul, hEn, smul_zero]

theorem exists_bilinForm (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) :
    ∃ B : LinearMap.BilinForm (ZMod 3) V, ∀ i v, B (h i) v = α i v := by
  have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ := span_eq_top_of_card hP hV
  have hsurj : Function.Surjective (Fintype.linearCombination (ZMod 3) h) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  obtain ⟨S, hS⟩ :=
    LinearMap.exists_rightInverse_of_surjective (Fintype.linearCombination (ZMod 3) h)
      (LinearMap.range_eq_top.mpr hsurj)
  have hFn : Fintype.linearCombination (ZMod 3) α cartanE6KernelVec = 0 := by
    refine LinearMap.ext_on_range (v := h) hspan fun k => ?_
    rw [Fintype.linearCombination_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, hP]
    exact cartanE6KernelVec_mulVec_transpose k
  have hES : ∀ w, Fintype.linearCombination (ZMod 3) h (S w) = w := by
    intro w
    simpa using LinearMap.congr_fun hS w
  have hsingle : ∀ i, Fintype.linearCombination (ZMod 3) h (Pi.single i 1) = h i := by
    intro i
    rw [Fintype.linearCombination_apply_single]
    simp
  have hFker : ∀ c : Fin 6 → ZMod 3,
      Fintype.linearCombination (ZMod 3) h c = 0 →
      Fintype.linearCombination (ZMod 3) α c = 0 := by
    intro c hc
    have hcC : cartanE6ModThree *ᵥ c = 0 := by
      ext i
      have h' := congrArg (α i) hc
      simp only [map_zero] at h'
      rwa [apply_linearCombination_eq_cartanE6ModThree hP i c] at h'
    have hcn : c = c 0 • cartanE6KernelVec := eq_smul_cartanE6KernelVec c hcC
    conv_lhs => rw [hcn]
    rw [map_smul, hFn, smul_zero]
  have hFS : ∀ i, Fintype.linearCombination (ZMod 3) α (S (h i)) = α i := by
    intro i
    have hker : Fintype.linearCombination (ZMod 3) h (S (h i) - Pi.single i 1) = 0 := by
      rw [map_sub, hES, hsingle, sub_self]
    have h0 : Fintype.linearCombination (ZMod 3) α (S (h i)) -
        Fintype.linearCombination (ZMod 3) α (Pi.single i 1) = 0 := by
      rw [← map_sub]
      exact hFker _ hker
    have h1 : Fintype.linearCombination (ZMod 3) α (Pi.single i 1) = α i := by
      rw [Fintype.linearCombination_apply_single]
      simp
    exact sub_eq_zero.mp (by rwa [h1] at h0)
  refine ⟨(Fintype.linearCombination (ZMod 3) α).comp S, fun i v => ?_⟩
  rw [LinearMap.comp_apply, hFS]

variable {B : LinearMap.BilinForm (ZMod 3) V}

theorem bilinForm_symm (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (u v : V) : B u v = B v u := by
  have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ := span_eq_top_of_card hP hV
  have hflip : B = B.flip := by
    refine LinearMap.ext_on_range (v := h) hspan fun i => ?_
    refine LinearMap.ext_on_range (v := h) hspan fun j => ?_
    rw [LinearMap.BilinForm.flip_apply, hB i (h j), hB j (h i), hP i j, hP j i]
    exact cartanE6ModThree_symm i j
  have h := LinearMap.congr_fun (LinearMap.congr_fun hflip u) v
  rwa [LinearMap.BilinForm.flip_apply] at h

theorem bilinForm_nondegenerate (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) {u : V}
    (hu : ∀ v, B u v = 0) : u = 0 := by
  refine eq_zero_of_forall_apply_eq_zero hP hV fun i => ?_
  rw [← hB i u, bilinForm_symm hP hV hB (h i) u]
  exact hu (h i)

theorem bilinForm_reflection (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (i : Fin 6) (u v : V) : B (reflection (hα i) u) (reflection (hα i) v) = B u v := by
  have hsymm := bilinForm_symm hP hV hB
  have hux : B u (h i) = α i u := by
    rw [hsymm u (h i)]
    exact hB i u
  have hvx : B v (h i) = α i v := by
    rw [hsymm v (h i)]
    exact hB i v
  have hxx : B (h i) (h i) = 2 := by rw [hB, hα]
  rw [reflection_apply, reflection_apply]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hB, hux, hvx, hxx, hα]
  ring

end CFSG.StandardType.E6QTwo

end
