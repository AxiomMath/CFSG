module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Module

public section

namespace CFSG.StandardType.FrameRoute

open Module

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem finrank_eq_three_mul_finrank_inf_ker_sub_one {ω : k} (hω : IsPrimitiveRoot ω 3)
    {x y : Module.End k W} {P : Submodule k W} (hxP : ∀ v ∈ P, x v ∈ P)
    (hyP : ∀ v ∈ P, y v ∈ P) (hx3 : x ^ 3 = 1) (hy : Function.Injective y)
    (hxy : x * y = ω • (y * x)) :
    finrank k P = 3 * finrank k ↥(P ⊓ LinearMap.ker (x - 1)) := by
  classical
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hω21 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    have h' : ω ^ 3 = ω ^ 2 * ω := pow_succ ω 2
    rw [hω3, h, one_mul] at h'
    exact h'.symm
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    have h2 : ω * ω = ω * 1 := by rw [mul_one, ← sq]; exact h.symm
    exact mul_left_cancel₀ hω0 h2
  have hsum : (1 : k) + ω + ω ^ 2 = 0 := by
    have h := hω.geom_sum_eq_zero (by norm_num : 1 < 3)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero] at h
    simpa using h
  have hsum' : (1 : k) + ω ^ 2 + ω = 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using hsum
  have hωsq : ω * ω = ω ^ 2 := (sq ω).symm
  have hωcube : ω * ω ^ 2 = 1 := by rw [← pow_succ', hω3]
  have hω2cube : ω ^ 2 * ω = 1 := by rw [← pow_succ, hω3]
  have hω4 : ω ^ 2 * ω ^ 2 = ω := by
    rw [← sq, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hω3, one_mul]
  have h3 : (3 : k) ≠ 0 := by
    haveI : NeZero ((3 : ℕ) : k) := hω.neZero'
    exact NeZero.ne (3 : k)
  let E : k → Submodule k W := fun t => P ⊓ Module.End.eigenspace x t
  have hE1 : E 1 = P ⊓ LinearMap.ker (x - 1) := by
    ext v
    simp only [E, Submodule.mem_inf, Module.End.mem_eigenspace_iff, one_smul,
      LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hy_mem : ∀ (t : k) (v : W), v ∈ E t → y v ∈ E (ω * t) := by
    intro t v hv
    obtain ⟨hvP, hveig⟩ := Submodule.mem_inf.mp hv
    refine Submodule.mem_inf.mpr ⟨hyP v hvP, ?_⟩
    rw [Module.End.mem_eigenspace_iff] at hveig ⊢
    calc x (y v) = (x * y) v := (Module.End.mul_apply x y v).symm
      _ = (ω • (y * x)) v := by rw [hxy]
      _ = ω • (y * x) v := LinearMap.smul_apply ω (y * x) v
      _ = ω • y (x v) := by rw [Module.End.mul_apply]
      _ = ω • y (t • v) := by rw [hveig]
      _ = ω • (t • y v) := by rw [map_smul]
      _ = (ω * t) • y v := smul_smul ω t (y v)
  have hy_le : ∀ t, finrank k (E t) ≤ finrank k (E (ω * t)) := by
    intro t
    let φ : (E t) →ₗ[k] (E (ω * t)) :=
      { toFun := fun v => ⟨y v, hy_mem t v v.2⟩
        map_add' := by intro u v; ext; simp
        map_smul' := by intro c v; ext; simp }
    have hinj : Function.Injective φ := by
      intro u v huv
      apply Subtype.ext
      exact hy (by simpa [φ] using congrArg Subtype.val huv)
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have h1 : finrank k (E 1) ≤ finrank k (E ω) := by
    have := hy_le 1
    rwa [mul_one] at this
  have h2 : finrank k (E ω) ≤ finrank k (E (ω ^ 2)) := by
    have := hy_le ω
    rwa [hωsq] at this
  have h3' : finrank k (E (ω ^ 2)) ≤ finrank k (E 1) := by
    have := hy_le (ω ^ 2)
    rwa [hωcube] at this
  have hEq1 : finrank k (E 1) = finrank k (E ω) := le_antisymm h1 (le_trans h2 h3')
  have hEq2 : finrank k (E 1) = finrank k (E (ω ^ 2)) := le_antisymm (le_trans h1 h2) h3'
  have hx3v : ∀ v : W, x (x (x v)) = v := by
    intro v
    have h := congrArg (fun f : Module.End k W => f v) hx3
    rw [Module.End.one_apply] at h
    rw [show x ^ 3 = (x * x) * x from by rw [pow_succ, pow_succ, pow_one],
      Module.End.mul_apply, Module.End.mul_apply] at h
    exact h
  have hspan : P ≤ E 1 ⊔ E ω ⊔ E (ω ^ 2) := by
    intro v hv
    have hx2vP : x (x v) ∈ P := hxP (x v) (hxP v hv)
    let a : W := (3 : k)⁻¹ • (v + x v + x (x v))
    let b : W := (3 : k)⁻¹ • (v + ω ^ 2 • x v + ω • x (x v))
    let d : W := (3 : k)⁻¹ • (v + ω • x v + ω ^ 2 • x (x v))
    have haP : a ∈ P := by
      dsimp only [a]
      exact P.smul_mem _ (P.add_mem (P.add_mem hv (hxP v hv)) hx2vP)
    have hbP : b ∈ P := by
      dsimp only [b]
      exact P.smul_mem _ (P.add_mem (P.add_mem hv (P.smul_mem _ (hxP v hv)))
        (P.smul_mem _ hx2vP))
    have hdP : d ∈ P := by
      dsimp only [d]
      exact P.smul_mem _ (P.add_mem (P.add_mem hv (P.smul_mem _ (hxP v hv)))
        (P.smul_mem _ hx2vP))
    have ha : a ∈ Module.End.eigenspace x 1 := by
      rw [Module.End.mem_eigenspace_iff]
      show x a = 1 • a
      rw [one_smul]
      dsimp only [a]
      simp only [map_smul, map_add, hx3v v]
      module
    have hb : b ∈ Module.End.eigenspace x ω := by
      rw [Module.End.mem_eigenspace_iff]
      show x b = ω • b
      dsimp only [b]
      simp only [map_smul, map_add, hx3v v]
      rw [smul_smul, mul_comm ω (3 : k)⁻¹, ← smul_smul]
      congr 1
      rw [smul_add, smul_add, smul_smul, smul_smul, hωcube, hωsq, one_smul]
      module
    have hd : d ∈ Module.End.eigenspace x (ω ^ 2) := by
      rw [Module.End.mem_eigenspace_iff]
      show x d = ω ^ 2 • d
      dsimp only [d]
      simp only [map_smul, map_add, hx3v v]
      rw [smul_smul, mul_comm (ω ^ 2) (3 : k)⁻¹, ← smul_smul]
      congr 1
      rw [smul_add, smul_add, smul_smul, smul_smul, hω2cube, hω4, one_smul]
      module
    have hav : a ∈ E 1 := Submodule.mem_inf.mpr ⟨haP, ha⟩
    have hbv : b ∈ E ω := Submodule.mem_inf.mpr ⟨hbP, hb⟩
    have hdv : d ∈ E (ω ^ 2) := Submodule.mem_inf.mpr ⟨hdP, hd⟩
    have habd : a + b + d = v := by
      have hS : (v + x v + x (x v)) + (v + ω ^ 2 • x v + ω • x (x v)) +
          (v + ω • x v + ω ^ 2 • x (x v)) = (3 : k) • v := by
        have hg : (v + x v + x (x v)) + (v + ω ^ 2 • x v + ω • x (x v)) +
            (v + ω • x v + ω ^ 2 • x (x v)) =
            (3 : k) • v + (1 + ω ^ 2 + ω) • x v + (1 + ω + ω ^ 2) • x (x v) := by
          module
        rw [hg, hsum, hsum', zero_smul, zero_smul, add_zero, add_zero]
      dsimp only [a, b, d]
      rw [← smul_add, ← smul_add, hS, smul_smul, inv_mul_cancel₀ h3, one_smul]
    have hmem : a + b + d ∈ E 1 ⊔ E ω ⊔ E (ω ^ 2) :=
      add_mem (add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left hav))
        (Submodule.mem_sup_left (Submodule.mem_sup_right hbv)))
        (Submodule.mem_sup_right hdv)
    rw [← habd]
    exact hmem
  have hEqP : P = E 1 ⊔ E ω ⊔ E (ω ^ 2) := by
    refine le_antisymm hspan ?_
    exact sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  have hdisj1 : Disjoint (E 1) (E ω) := by
    rw [disjoint_iff_inf_le]
    intro u hu
    rw [Submodule.mem_bot]
    obtain ⟨hu1, huω⟩ := Submodule.mem_inf.mp hu
    simp only [E, Submodule.mem_inf] at hu1 huω
    rw [Module.End.mem_eigenspace_iff] at hu1 huω
    have h1' : x u = u := by rw [hu1.2, one_smul]
    have hω' : x u = ω • u := huω.2
    have h0 : (1 - ω) • u = 0 := by
      rw [sub_smul, one_smul]
      nth_rewrite 1 [h1'.symm]
      rw [hω', sub_self]
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hω1))
  have hdisj2 : Disjoint (E (ω ^ 2)) (E 1 ⊔ E ω) := by
    refine ((Module.End.eigenspaces_iSupIndep x) (ω ^ 2)).mono inf_le_right ?_
    refine sup_le ?_ ?_
    · refine le_trans inf_le_right ?_
      refine le_trans (le_iSup (fun _ : (1 : k) ≠ ω ^ 2 => Module.End.eigenspace x 1)
        (Ne.symm hω21)) ?_
      exact le_iSup (fun j => ⨆ (_ : j ≠ ω ^ 2), Module.End.eigenspace x j) 1
    · refine le_trans inf_le_right ?_
      refine le_trans (le_iSup (fun _ : ω ≠ ω ^ 2 => Module.End.eigenspace x ω) hωω2) ?_
      exact le_iSup (fun j => ⨆ (_ : j ≠ ω ^ 2), Module.End.eigenspace x j) ω
  have hE1Eω : E 1 ⊓ E ω = ⊥ := hdisj1.eq_bot
  have hE12 : (E 1 ⊔ E ω) ⊓ E (ω ^ 2) = ⊥ := by
    rw [inf_comm]
    exact hdisj2.eq_bot
  have hd1 := Submodule.finrank_sup_add_finrank_inf_eq (E 1) (E ω)
  rw [hE1Eω, finrank_bot, add_zero] at hd1
  have hd2 := Submodule.finrank_sup_add_finrank_inf_eq (E 1 ⊔ E ω) (E (ω ^ 2))
  rw [hE12, finrank_bot, add_zero] at hd2
  have hdim : finrank k P = 3 * finrank k (E 1) := by
    rw [hEqP, hd2, hd1, ← hEq1, ← hEq2]
    ring
  rw [hdim, hE1]

end CFSG.StandardType.FrameRoute

end
