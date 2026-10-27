module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2s08x2c_span_singleton_mem
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {x : V}
    {T : V →ₗ[ZMod 3] V} (hT : T x = x) {s : V}
    (hs : s ∈ Submodule.span (ZMod 3) ({x} : Set V)) :
    T s ∈ Submodule.span (ZMod 3) ({x} : Set V) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
  rw [← hc, map_smul, hT]
  exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton x))

theorem ggQ2s08x2_inj
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hx : x ∈ Bs) (M : GGQ2LDatum 3 Bs L x)
    (ψ₁ ψ₂ : MulAut ↥Bs)
    (h₁ : ψ₁ ∈ ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs))
    (h₂ : ψ₂ ∈ ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs))
    (h : ∀ v : M.V,
      (Submodule.Quotient.mk (ggLin (p := 3) M.model ψ₁ v) : M.V ⧸ Submodule.span (ZMod 3) {M.xV}) =
        Submodule.Quotient.mk (ggLin (p := 3) M.model ψ₂ v)) :
    ψ₁ = ψ₂ := by
  set T : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model ψ₁ with hT
  set U : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model ψ₂ with hU
  set χ : MulAut ↥Bs := ψ₁⁻¹ * ψ₂ with hχ
  have hx_ne_one : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hxV0 : M.xV ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by simpa [GGQ2LDatum.xV, map_zero] using h0)
    have h2 : (⟨x, M.hx⟩ : ↥Bs) = 1 := ofMul_eq_zero.mp h1
    exact hx_ne_one (Subtype.ext_iff.mp h2)
  have hψ1x' : ψ₁ (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
    have hh := MulAction.mem_stabilizer_iff.mp
      (show ψ₁ ∈ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs) from h₁.2)
    simpa [MulAut.smul_def] using hh
  have hψ2x' : ψ₂ (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
    have hh := MulAction.mem_stabilizer_iff.mp
      (show ψ₂ ∈ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs) from h₂.2)
    simpa [MulAut.smul_def] using hh
  have hpt : (⟨x, M.hx⟩ : ↥Bs) = ⟨x, hx⟩ := Subtype.ext rfl
  have hψ1x : ψ₁ (⟨x, M.hx⟩ : ↥Bs) = ⟨x, M.hx⟩ := by rw [hpt, hψ1x']
  have hψ2x : ψ₂ (⟨x, M.hx⟩ : ↥Bs) = ⟨x, M.hx⟩ := by rw [hpt, hψ2x']
  have hT_xV : T M.xV = M.xV := by
    rw [hT, GGQ2LDatum.xV, ggLin_apply_ofMul, hψ1x]
  have hU_xV : U M.xV = M.xV := by
    rw [hU, GGQ2LDatum.xV, ggLin_apply_ofMul, hψ2x]
  have hT_inv_xV : T.symm M.xV = M.xV := by
    have hh := congrArg (fun w => T.symm w) hT_xV
    simpa using hh.symm
  have hχv : ∀ v : M.V, ggLin (p := 3) M.model χ v = T.symm (U v) := by
    intro v
    rw [hχ]
    simp only [map_mul, map_inv, ← hT, ← hU, LinearEquiv.mul_apply]
    rfl
  have hχ_xV : ggLin (p := 3) M.model χ M.xV = M.xV := by
    rw [hχv M.xV, hU_xV, hT_inv_xV]
  set S : Submodule (ZMod 3) M.V := Submodule.span (ZMod 3) ({M.xV} : Set M.V) with hSdef
  have hg : ∀ v : M.V, ggLin (p := 3) M.model χ v - v ∈ S := by
    intro v
    have hv : T v - U v ∈ S := by
      have hh := h v
      rw [Submodule.Quotient.eq] at hh
      exact hh
    have h2 : U v - T v ∈ S := by
      have hneg := Submodule.neg_mem S hv
      rwa [neg_sub] at hneg
    have h3 : T.symm (U v - T v) ∈ S :=
      ggQ2s08x2c_span_singleton_mem (T := (T.symm : M.V →ₗ[ZMod 3] M.V)) hT_inv_xV h2
    have h4 : T.symm (U v - T v) = ggLin (p := 3) M.model χ v - v := by
      rw [map_sub, LinearEquiv.symm_apply_apply, hχv v]
    rwa [h4] at h3
  let g : M.V →ₗ[ZMod 3] M.V := (ggLin (p := 3) M.model χ).toLinearMap - LinearMap.id
  have hg_apply : ∀ v : M.V, g v = ggLin (p := 3) M.model χ v - v := by
    intro v
    simp [g]
  have hg_mem : ∀ v : M.V, g v ∈ S := by
    intro v
    rw [hg_apply v]
    exact hg v
  let e : S ≃ₗ[ZMod 3] ZMod 3 := LinearEquiv.coord (ZMod 3) M.V M.xV hxV0
  let f : Module.Dual (ZMod 3) M.V := (e : S →ₗ[ZMod 3] ZMod 3).comp (g.codRestrict S hg_mem)
  have hf_smul : ∀ v : M.V, f v • M.xV = g v := by
    intro v
    have hh := LinearEquiv.coord_apply_smul (ZMod 3) M.V M.xV hxV0 (⟨g v, hg_mem v⟩ : S)
    exact hh
  have hf_xV : f M.xV = 0 := by
    have hh := hf_smul M.xV
    have hg0 : g M.xV = 0 := by rw [hg_apply M.xV, hχ_xV, sub_self]
    rw [hg0] at hh
    exact (smul_eq_zero.mp hh).resolve_right hxV0
  have hχ_ind : χ ∈ ggInduced ⊤ Bs := by
    have hmem : χ ∈ ggInducedSubgroup ⊤ Bs := by
      rw [← ggAutomizer_eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁.1) h₂.1
    exact hmem
  by_cases hf : f = 0
  ·
    have hlin : ggLin (p := 3) M.model χ = 1 := by
      refine LinearEquiv.ext fun v => ?_
      show ggLin (p := 3) M.model χ v = v
      have hh := hf_smul v
      rw [hf] at hh
      simp only [LinearMap.zero_apply, zero_smul] at hh
      rw [hg_apply v] at hh
      exact eq_of_sub_eq_zero hh.symm
    have hχ1 : χ = 1 := ggLin_injective (p := 3) M.model (by simpa using hlin)
    have h1 : ψ₁⁻¹ * ψ₂ = 1 := by rw [← hχ, hχ1]
    calc ψ₁ = ψ₁ * (ψ₁⁻¹ * ψ₂) := by rw [h1, mul_one]
      _ = ψ₂ := by group
  ·
    have htrans : GGIsTransvection 3 χ := by
      refine ggIsTransvection_of_apply (p := 3) M.model hxV0 hf hf_xV ?_
      intro v
      have hh : f v • M.xV = ggLin (p := 3) M.model χ v - v := by
        rw [hf_smul v, hg_apply v]
      rw [eq_sub_iff_add_eq] at hh
      rw [add_comm]
      exact hh.symm
    exact absurd htrans (hS.1.2.2.2.1 χ hχ_ind)
