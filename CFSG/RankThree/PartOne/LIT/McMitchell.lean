module

public import CFSG.RankThree.SubgroupLists.TransvectionRecognition
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.RankThree.PartOne.KC.AlternatingSymplecticBasis

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coordinates

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def autGL (e : V ≃ₗ[K] (σ → K)) : (V ≃ₗ[K] V) ≃* GL σ K :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e)).trans
    (Matrix.GeneralLinearGroup.toLin (n := σ) (R := K)).symm

theorem autGL_mulVec (e : V ≃ₗ[K] (σ → K)) (g : V ≃ₗ[K] V) (v : σ → K) :
    ((autGL e g : GL σ K) : Matrix σ σ K) *ᵥ v = e (g (e.symm v)) := by
  have h : Matrix.GeneralLinearGroup.toLin (autGL e g) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv e
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm g) := by
    simp [autGL]
  exact congrArg (fun f : ((σ → K) →ₗ[K] (σ → K))ˣ => f.val v) h

theorem isIrreducibleOn_map_autGL (e : V ≃ₗ[K] (σ → K)) {H : Subgroup (V ≃ₗ[K] V)}
    (hirr : ∀ W : Submodule K V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤) :
    IsIrreducibleOn (H.map (autGL e).toMonoidHom) := by
  intro W hW
  have hinv : ∀ h ∈ H, ∀ x ∈ W.comap (e : V →ₗ[K] (σ → K)),
      h x ∈ W.comap (e : V →ₗ[K] (σ → K)) := by
    intro h hh x hx
    rw [Submodule.mem_comap] at hx ⊢
    have := hW (autGL e h) (Subgroup.mem_map_of_mem _ hh) (e x) hx
    rwa [autGL_mulVec, LinearEquiv.symm_apply_apply] at this
  rcases hirr _ hinv with h | h
  · refine Or.inl (eq_bot_iff.mpr fun w hw => ?_)
    have hmem : e.symm w ∈ W.comap (e : V →ₗ[K] (σ → K)) := by
      rw [Submodule.mem_comap]
      simpa using hw
    rw [h, Submodule.mem_bot] at hmem
    simpa using congrArg e hmem
  · refine Or.inr (eq_top_iff.mpr fun w _ => ?_)
    have hmem : e.symm w ∈ W.comap (e : V →ₗ[K] (σ → K)) := by
      rw [h]
      exact Submodule.mem_top
    simpa using hmem

end Coordinates

section Symplectic

variable {K : Type} [Field K] {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]

theorem autGL_mem_statedSp_iff {B : LinearMap.BilinForm K V}
    {e : V ≃ₗ[K] (Fin n ⊕ Fin n → K)} (he : ∀ x y, spForm n K (e x) (e y) = B x y)
    (g : V ≃ₗ[K] V) : autGL e g ∈ StatedSp n K ↔ ∀ x y, B (g x) (g y) = B x y := by
  rw [mem_statedSp_iff_preserves]
  constructor
  · intro h x y
    have := h (e x) (e y)
    rwa [autGL_mulVec, autGL_mulVec, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      he, he] at this
  · intro h x y
    rw [autGL_mulVec, autGL_mulVec, he, h, ← he, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

end Symplectic

theorem eq_isometries_of_perfect_irreducible {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 4)
    (B : LinearMap.BilinForm (ZMod p) V) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hHB : ∀ g ∈ H, ∀ x y, B (g x) (g y) = B x y)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    [Group.IsPerfect H] {a : V} (ha : a ≠ 0) {c : ZMod p} (hc : c ≠ 0)
    (hT : ∃ t ∈ H, ∀ x, t x = x + (c * B x a) • a) :
    ∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ ∀ x y, B (g x) (g y) = B x y := by
  have hrank : Module.finrank (ZMod p) V =
      Module.finrank (ZMod p) (Fin 2 ⊕ Fin 2 → ZMod p) := by
    rw [hdim, Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨e, he⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isometry_of_finrank_eq hB hBnd
    spForm_isAlt spForm_nondegenerate hrank
  have : Group.IsPerfect (H.map (autGL e).toMonoidHom) := Group.IsPerfect.map _
  have hGS : H.map (autGL e).toMonoidHom ≤ StatedSp 2 (ZMod p) := by
    rintro _ ⟨g, hg, rfl⟩
    exact (autGL_mem_statedSp_iff he g).mpr (hHB g hg)
  obtain ⟨t, htH, ht⟩ := hT
  have hea : e a ≠ 0 := fun h => ha (e.injective (by rw [h, map_zero]))
  have htrans : autGL e t = spTrans (e a) c := by
    refine gl_ext_mulVec fun x => ?_
    rw [autGL_mulVec, spTrans_mulVec, ht, map_add, map_smul, LinearEquiv.apply_symm_apply,
      ← he (e.symm x) a, LinearEquiv.apply_symm_apply]
  have hG := eq_statedSp_of_spTrans_mem hp2 hGS (isIrreducibleOn_map_autGL e hirr) hea hc
    (htrans ▸ Subgroup.mem_map_of_mem (autGL e).toMonoidHom htH)
  intro g
  refine ⟨hHB g, fun hg => ?_⟩
  have hmem : autGL e g ∈ H.map (autGL e).toMonoidHom := by
    rw [hG]
    exact (autGL_mem_statedSp_iff he g).mpr hg
  obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.mp hmem
  exact (autGL e).injective hhg ▸ hh

end CFSG.RankThree.PartOne.LIT
