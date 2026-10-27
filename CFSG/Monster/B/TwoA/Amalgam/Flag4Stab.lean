module

public import CFSG.Monster.B.TwoA.Amalgam.OrthWitt
public import CFSG.Monster.B.TwoA.Amalgam.Kernels

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open Module Submodule CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

abbrev flag4W
    (j : Fin 3) : Submodule (ZMod 2) V8 := a8Vec (Echain ((j : ℕ) + 1))

theorem qForm_bvec_std : ∀ a ∈ [1, 2, 4], qForm (bvec 8 a) = 0 := by
  intro a ha
  rw [qForm_apply]
  revert a
  decide +kernel

theorem polar_qForm_bvec_std : ∀ a ∈ [1, 2, 4], ∀ c ∈ [1, 2, 4],
    QuadraticMap.polar qForm (bvec 8 a) (bvec 8 c) = 0 := by
  intro a ha c hc
  rw [← QuadraticMap.polarBilin_apply_apply, polarBilin_qForm, b0_apply]
  revert a c
  decide +kernel

theorem qForm_eq_zero_of_mem_E3
    {v : V8} (hv : v ∈ a8Vec E3) : qForm v = 0 := by
  have h3 : a8Vec E3 = span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 4} :=
    a8Vec_Echain (i := 3) (by norm_num) (by norm_num)
  rw [h3] at hv
  refine CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span (fun u hu => ?_)
    (fun u hu w hw => ?_) hv
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl <;> exact qForm_bvec_std _ (by simp)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      exact polar_qForm_bvec_std _ (by simp) _ (by simp)

theorem flag4W_mono :
    Monotone flag4W := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  have hj := j.isLt
  exact a8Vec_mono (Echain_mono (by omega) (by omega) (by omega))

theorem flag4W_le_E3
    (j : Fin 3) : flag4W j ≤ a8Vec E3 := by
  have hj := j.isLt
  exact a8Vec_mono (Echain_mono (i := (j : ℕ) + 1) (j := 3) (by omega) (by omega) (by norm_num))

theorem flag4W_mem
    (j : Fin 3) : flag4W j ∈ singularSubspaces qForm ((j : ℕ) + 1) := by
  have hj := j.isLt
  exact ⟨finrank_a8Vec_Echain (by omega) (by omega),
    fun _ hv => qForm_eq_zero_of_mem_E3 (flag4W_le_E3 j hv)⟩

theorem flag4W_mem_singularFlags :
    flag4W ∈ singularFlags qForm 3 :=
  ⟨fun j => (flag4W_mem j).1, flag4W_mono, fun j => (flag4W_mem j).2⟩

theorem Pc_castSucc
    (j : Fin 3) :
    Pc j.castSucc = Kchain ((j : ℕ) + 1) ⊓ Subgroup.centralizer {cQ} := by
  fin_cases j
  · exact congrArg (· ⊓ Subgroup.centralizer {cQ}) Kchain_one.symm
  · rfl
  · rfl

theorem mem_Kchain_iff_map
    (x : Xgrp) {i : ℕ} (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    (x : Dfull) ∈ Kchain i ↔
      (a8Vec (Echain i)).map (rhoX x : V8 →ₗ[ZMod 2] V8) = a8Vec (Echain i) := by
  rw [← a8Vec_conjSub x (Echain_le_A8 h1 h4)]
  constructor
  · intro h
    rw [conjSub_eq_self_iff.2 h]
  · intro h
    exact conjSub_eq_self_iff.1
      (a8Vec_injective (conjSub_le_A8 x.2 (Echain_le_A8 h1 h4)) (Echain_le_A8 h1 h4) h)

abbrev flag4H
    (j : Fin 3) : Subgroup P4 := (Pc 3 ⊓ Pc j.castSucc).subgroupOf P4

theorem mem_flag4H_iff
    (j : Fin 3) (x : P4) :
    x ∈ flag4H j ↔ (flag4W j).map (p4Proj x : V8 →ₗ[ZMod 2] V8) = flag4W j := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Pc_castSucc, Subgroup.mem_inf]
  have hj := j.isLt
  have h := mem_Kchain_iff_map (Subgroup.inclusion P4_le_Xgrp x) (i := (j : ℕ) + 1) (by omega)
    (by omega)
  exact ⟨fun hx => h.1 hx.2.1, fun hx => ⟨x.2, h.2 hx, x.2.2⟩⟩

theorem flag4H_eq
    (j : Fin 3) :
    flag4H j = (MulAction.stabilizer (TauCeti.QuadraticMap.orthogonalGroup qForm)
      (flag4W j)).comap p4Proj := by
  ext x
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  exact mem_flag4H_iff j x

theorem map_p4Proj_mul
    (a b : P4) (W : Submodule (ZMod 2) V8) :
    W.map (p4Proj (a * b) : V8 →ₗ[ZMod 2] V8) =
      (W.map (p4Proj b : V8 →ₗ[ZMod 2] V8)).map (p4Proj a : V8 →ₗ[ZMod 2] V8) := by
  rw [map_mul, Subgroup.coe_mul, map_mul_linearEquiv]

theorem map_p4Proj_one
    (W : Submodule (ZMod 2) V8) :
    W.map (p4Proj 1 : V8 →ₗ[ZMod 2] V8) = W := by
  rw [map_one]
  exact Submodule.map_id W

theorem map_p4Proj_mem
    {k : ℕ} (g : P4) {X : Submodule (ZMod 2) V8}
    (hX : X ∈ singularSubspaces qForm k) :
    X.map (p4Proj g : V8 →ₗ[ZMod 2] V8) ∈ singularSubspaces qForm k := by
  refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact hX.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearEquiv.coe_coe, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (p4Proj g).2]
  exact hX.2 x hx

theorem exists_p4_map_eq
    (j : Fin 3) {X : Submodule (ZMod 2) V8}
    (hX : X ∈ singularSubspaces qForm ((j : ℕ) + 1)) :
    ∃ g : P4, (flag4W j).map (p4Proj g : V8 →ₗ[ZMod 2] V8) = X := by
  have hj := j.isLt
  obtain ⟨M, hM, hMX⟩ := qForm_subspace_transitive (by omega) (flag4W_mem j) hX
  obtain ⟨g, hg⟩ := p4Proj_surjective ⟨M, hM⟩
  refine ⟨g, ?_⟩
  rw [hg]
  exact hMX

theorem eq_one_of_map_points {M : V8 ≃ₗ[ZMod 2] V8}
    (h : ∀ X ∈ singularSubspaces qForm 1, X.map (M : V8 →ₗ[ZMod 2] V8) = X) : M = 1 := by
  have hfix : ∀ v : V8, qPoly v = 0 → M v = v := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    have hX : span (ZMod 2) {v} ∈ singularSubspaces qForm 1 := by
      refine ⟨finrank_span_singleton hv0, fun x hx => ?_⟩
      obtain ⟨c, rfl⟩ := mem_span_singleton.1 hx
      rw [QuadraticMap.map_smul, qForm_apply, hv, smul_zero]
    have hmem : M v ∈ span (ZMod 2) {v} := by
      rw [← h _ hX]
      exact ⟨v, mem_span_singleton_self v, rfl⟩
    obtain ⟨c, hc⟩ := mem_span_singleton.1 hmem
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul] at hc
      exact absurd (M.injective (hc.symm.trans (map_zero M).symm)) hv0
    · rw [one_smul] at hc
      exact hc.symm
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun (ZMod 2) (Fin 8)).ext fun k => ?_
  obtain ⟨a, b, ha, hb, hab⟩ := zeros_span k
  change M (Pi.basisFun (ZMod 2) (Fin 8) k) = Pi.basisFun (ZMod 2) (Fin 8) k
  rw [Pi.basisFun_apply, ← hab, map_add, hfix a ha, hfix b hb]

theorem Lgrp_le_Pc
    (j : Fin 4) : Lgrp ≤ Pc j := by
  fin_cases j
  · exact le_inf Lgrp_le_Jhat Lgrp_le_centralizer
  · exact le_inf Lgrp_le_Ntwo Lgrp_le_centralizer
  · exact le_inf Lgrp_le_K3 Lgrp_le_centralizer
  · exact Lgrp_le_P4

theorem iInf_conjSub_eq_Nc :
    (⨅ (j : Fin 4) (_ : j ≠ 3) (g : P4), conjSub (g : Dfull) (Pc 3 ⊓ Pc j)) = Nc 3 := by
  rw [Nc_three]
  refine le_antisymm (fun x hx => ?_) (le_iInf fun j => le_iInf fun _ => le_iInf fun g => ?_)
  · have hx0 : ∀ g : P4, (g : Dfull)⁻¹ * x * g ∈ Pc 3 ⊓ Pc 0 := fun g =>
      mem_conjSub.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx 0)
        (by decide)) g)
    have hxP : x ∈ P4 := by
      have h := (hx0 1).1
      rwa [OneMemClass.coe_one, inv_one, one_mul, mul_one] at h
    set y : P4 := ⟨x, hxP⟩ with hy
    have hstab : ∀ X ∈ singularSubspaces qForm 1,
        X.map (p4Proj y : V8 →ₗ[ZMod 2] V8) = X := by
      intro X hX
      obtain ⟨g, rfl⟩ := exists_p4_map_eq 0 hX
      have h1 : g⁻¹ * y * g ∈ flag4H 0 := by
        rw [Subgroup.mem_subgroupOf]
        exact hx0 g
      rw [mem_flag4H_iff] at h1
      rw [← map_p4Proj_mul, show y * g = g * (g⁻¹ * y * g) by group, map_p4Proj_mul, h1]
    have hone : p4Proj y = 1 := Subtype.ext (eq_one_of_map_points hstab)
    have hker : y ∈ p4Proj.ker := MonoidHom.mem_ker.2 hone
    rw [ker_p4Proj, Subgroup.mem_subgroupOf] at hker
    exact hker
  · intro x hx
    rw [mem_conjSub]
    have hn := (Lgrp_subgroupOf_P4_normal).conj_mem ⟨x, Lgrp_le_P4 hx⟩
      (Subgroup.mem_subgroupOf.2 hx) g⁻¹
    rw [Subgroup.mem_subgroupOf] at hn
    have hL : (g : Dfull)⁻¹ * x * g ∈ Lgrp := by simpa using hn
    exact ⟨Lgrp_le_Pc 3 hL, Lgrp_le_Pc j hL⟩

end CFSG.Monster.B.TwoA.Amalgam
