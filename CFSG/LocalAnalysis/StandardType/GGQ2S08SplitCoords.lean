module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggQ2RootCoordRefl {Λ : Type} (C : Matrix Λ Λ ℤ) (i : Λ) (v : Option Λ → ZMod 3) :
    Option Λ → ZMod 3
  | none => v none
  | some j => v (some j) - v (some i) * (C j i : ZMod 3)

theorem ggQ2LDatum_rootCoords {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hρ : Function.Surjective M.rootMap) (hx : M.xV ∉ M.coSpan) :
    ∃ κ : M.V ≃ₗ[ZMod 3] (Option M.Λ → ZMod 3), κ M.xV = Pi.single none 1 ∧
      (∀ v, ∀ j : M.Λ, κ v (some j) = M.root j v) ∧
      ∀ (i : M.Λ) (v : Option M.Λ → ZMod 3),
        κ (ggLin (p := 3) M.model (M.simple i) (κ.symm v)) = ggQ2RootCoordRefl M.cartan i v := by
  have hxV_fixed : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.subset_span (Set.mem_singleton M.xV)
  have hsimple_mem : ∀ i, M.simple i ∈ ggAutomizer L Bs := by
    intro i
    rw [M.automizer_L]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hxV_root : ∀ i, M.root i M.xV = 0 := by
    intro i
    have hfix : ggLin (p := 3) M.model (M.simple i) M.xV = M.xV :=
      (mem_ggFixedSubmodule_iff.mp hxV_fixed) (M.simple i) (hsimple_mem i)
    rw [M.simple_apply i M.xV] at hfix
    have h0 : (M.root i M.xV) • M.coroot i = 0 := sub_eq_self.mp hfix
    have h2 : (M.root i M.xV) * (M.cartan i i : ZMod 3) = 0 := by
      have := congrArg (fun w => M.root i w) h0
      simpa [map_smul, M.pairing i i, smul_eq_mul, RingHom.id_apply] using this
    have hc2 : (M.cartan i i : ZMod 3) = 2 := by
      rw [M.isCartan.1 i]
      norm_num
    rw [hc2] at h2
    exact (mul_eq_zero.mp h2).resolve_right (by decide : (2 : ZMod 3) ≠ 0)
  have hrootMap_xV : M.rootMap M.xV = 0 := by
    funext i
    change M.root i M.xV = 0
    rw [hxV_root i]
  have hker_le : ∀ v : M.V, M.rootMap v = 0 → v ∈ Submodule.span (ZMod 3) {M.xV} := by
    intro v hv
    have hroot : ∀ i, M.root i v = 0 := by
      intro i
      have := congrFun hv i
      simpa [GGQ2LDatum.rootMap] using this
    have hfix_simple : ∀ i, ggLin (p := 3) M.model (M.simple i) v = v := by
      intro i
      rw [M.simple_apply i v, hroot i, zero_smul, sub_zero]
    let K : Subgroup (MulAut ↥Bs) :=
      { carrier := {φ | ggLin (p := 3) M.model φ v = v}
        one_mem' := by
          simp only [Set.mem_setOf_eq]
          rw [map_one]
          rfl
        mul_mem' := by
          intro φ ψ hφ hψ
          simp only [Set.mem_setOf_eq] at hφ hψ ⊢
          rw [map_mul, LinearEquiv.mul_apply, hψ, hφ]
        inv_mem' := by
          intro φ hφ
          simp only [Set.mem_setOf_eq] at hφ ⊢
          apply (ggLin (p := 3) M.model φ).injective
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rw [hφ]
          rfl }
    have hK : Subgroup.closure (Set.range M.simple) ≤ K := by
      rw [Subgroup.closure_le]
      rintro φ ⟨i, rfl⟩
      exact hfix_simple i
    have hfix_all : ∀ φ ∈ ggAutomizer L Bs, ggLin (p := 3) M.model φ v = v := by
      intro φ hφ
      rw [M.automizer_L] at hφ
      exact hK hφ
    have hmem : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) :=
      mem_ggFixedSubmodule_iff.mpr hfix_all
    rw [M.fixed_x] at hmem
    simpa only [GGQ2LDatum.xV] using hmem
  obtain ⟨f, hfv, hfker⟩ := Submodule.exists_le_ker_of_notMem hx
  let ξ : M.V →ₗ[ZMod 3] ZMod 3 := (f M.xV)⁻¹ • f
  have hξx : ξ M.xV = 1 := by
    simp only [ξ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfv
  have hξ_cospan : ∀ u ∈ M.coSpan, ξ u = 0 := by
    intro u hu
    simp only [ξ, LinearMap.smul_apply, smul_eq_mul, LinearMap.mem_ker.mp (hfker hu), mul_zero]
  have hξ_coroot : ∀ j, ξ (M.coroot j) = 0 := by
    intro j
    exact hξ_cospan _ (Submodule.subset_span (Set.mem_range_self j))
  let κLin : M.V →ₗ[ZMod 3] (Option M.Λ → ZMod 3) :=
    LinearMap.pi (fun o => Option.rec ξ (fun j => M.root j) o)
  have hκLin_none : ∀ v, κLin v none = ξ v := fun v => rfl
  have hκLin_some : ∀ v j, κLin v (some j) = M.root j v := fun v j => rfl
  have hκ_inj : Function.Injective κLin := by
    intro u v huv
    have hzero : κLin (u - v) = 0 := by
      rw [map_sub]
      funext o
      exact sub_eq_zero.mpr (congrFun huv o)
    have hroot : M.rootMap (u - v) = 0 := by
      funext j
      have := congrFun hzero (some j)
      simpa [hκLin_some, GGQ2LDatum.rootMap] using this
    have hmem : u - v ∈ Submodule.span (ZMod 3) {M.xV} := hker_le (u - v) hroot
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hξzero : ξ (u - v) = 0 := by
      have := congrFun hzero none
      simpa [hκLin_none] using this
    rw [← hc, map_smul, hξx, smul_eq_mul, mul_one] at hξzero
    have hsub : u - v = 0 := by
      rw [← hc, hξzero, zero_smul]
    exact sub_eq_zero.mp hsub
  have hκ_surj : Function.Surjective κLin := by
    intro w
    obtain ⟨v₀, hv₀⟩ := hρ (fun j => w (some j))
    refine ⟨v₀ + (w none - ξ v₀) • M.xV, ?_⟩
    funext o
    cases o with
    | none =>
        rw [hκLin_none, map_add, map_smul, hξx, smul_eq_mul, mul_one]
        ring
    | some j =>
        rw [hκLin_some, map_add, map_smul, hxV_root j, smul_eq_mul, mul_zero, add_zero]
        have := congrFun hv₀ j
        simpa [GGQ2LDatum.rootMap] using this
  let κ : M.V ≃ₗ[ZMod 3] (Option M.Λ → ZMod 3) :=
    LinearEquiv.ofBijective κLin ⟨hκ_inj, hκ_surj⟩
  have hκ_none : ∀ v, κ v none = ξ v := by
    intro v
    change κLin v none = ξ v
    rfl
  have hκ_some : ∀ v j, κ v (some j) = M.root j v := by
    intro v j
    change κLin v (some j) = M.root j v
    rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · funext o
    cases o with
    | none =>
        rw [hκ_none, hξx]
        simp
    | some j =>
        rw [hκ_some, hxV_root j]
        simp
  · intro v j
    exact hκ_some v j
  · intro i v
    have hξ_symm : ξ (κ.symm v) = v none := by
      rw [← hκ_none (κ.symm v), LinearEquiv.apply_symm_apply]
    have hroot_symm : ∀ j, M.root j (κ.symm v) = v (some j) := by
      intro j
      rw [← hκ_some (κ.symm v) j, LinearEquiv.apply_symm_apply]
    funext o
    cases o with
    | none =>
        rw [hκ_none, M.simple_apply i (κ.symm v), map_sub, map_smul, hξ_coroot i]
        simp only [smul_eq_mul, mul_zero, hξ_symm]
        rw [show ggQ2RootCoordRefl M.cartan i v none = v none from rfl]
        abel
    | some j =>
        rw [hκ_some, M.simple_apply i (κ.symm v), map_sub, map_smul, M.pairing j i,
          smul_eq_mul, hroot_symm j, hroot_symm i]
        rfl

end CFSG.StandardType

end
