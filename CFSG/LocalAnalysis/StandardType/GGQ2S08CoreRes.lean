module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs
public import CFSG.LocalAnalysis.StandardType.GGWAutCommon

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2S08Res {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (H : Submodule (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H) :
    Subgroup (↥H ≃ₗ[ZMod 3] ↥H) where
  carrier := {b | ∃ a ∈ R, ∀ h : ↥H, ((b h : ↥H) : V) = a h}
  mul_mem' := by
    rintro b₁ b₂ ⟨a₁, ha₁R, h₁⟩ ⟨a₂, ha₂R, h₂⟩
    refine ⟨a₁ * a₂, R.mul_mem ha₁R ha₂R, ?_⟩
    intro h
    rw [LinearEquiv.mul_apply, h₁ (b₂ h), h₂ h, LinearEquiv.mul_apply]
  one_mem' := by
    refine ⟨1, R.one_mem, ?_⟩
    intro h
    rfl
  inv_mem' := by
    rintro b ⟨a, haR, hb⟩
    refine ⟨a⁻¹, R.inv_mem haR, ?_⟩
    intro h
    have hb1 : ((b (b⁻¹ h) : ↥H) : V) = a ((b⁻¹ h : ↥H) : V) := hb (b⁻¹ h)
    have hbb : b (b⁻¹ h) = h := by
      simpa [LinearEquiv.coe_inv] using LinearEquiv.apply_symm_apply b h
    have key : a ((b⁻¹ h : ↥H) : V) = (h : V) := by
      rw [← hb1, hbb]
    have key2 : ((b⁻¹ h : ↥H) : V) = a⁻¹ (h : V) := by
      have := congrArg (fun x : V => a.symm x) key
      simpa [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using this
    exact key2

private theorem ggQ2s08k11_res_mem_aux {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H) (a : V ≃ₗ[ZMod 3] V) (haR : a ∈ R) :
    ∃ b ∈ GGQ2S08Res H R hRH, ∀ h : ↥H, ((b h : ↥H) : V) = a h := by
  let f : ↥H →ₗ[ZMod 3] ↥H :=
    { toFun := fun x => ⟨a x, hRH a haR x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun r x => Subtype.ext (by simp) }
  let g : ↥H →ₗ[ZMod 3] ↥H :=
    { toFun := fun x => ⟨a⁻¹ x, hRH a⁻¹ (R.inv_mem haR) x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun r x => Subtype.ext (by simp) }
  have h₁ : f.comp g = LinearMap.id := by
    ext x
    change a (a⁻¹ (x : V)) = (x : V)
    exact LinearEquiv.apply_symm_apply a (x : V)
  have h₂ : g.comp f = LinearMap.id := by
    ext x
    change a⁻¹ (a (x : V)) = (x : V)
    exact LinearEquiv.symm_apply_apply a (x : V)
  let b : ↥H ≃ₗ[ZMod 3] ↥H := LinearEquiv.ofLinear f g h₁ h₂
  refine ⟨b, ?_, ?_⟩
  · refine ⟨a, haR, ?_⟩
    intro h
    rw [LinearEquiv.ofLinear_apply]
    rfl
  · intro h
    rw [LinearEquiv.ofLinear_apply]
    rfl

theorem ggQ2s08core_res_refl {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H) (a : V ≃ₗ[ZMod 3] V)
    (haR : a ∈ R) (ha : GGLinRefl a) (hne : ∃ h ∈ H, a h ≠ h) :
    ∃ b ∈ GGQ2S08Res H R hRH, (∀ h : ↥H, ((b h : ↥H) : V) = a h) ∧ GGLinRefl b := by
  have ha2 : a * a = 1 := ha.1
  obtain ⟨c, φ, hφc, haeq⟩ := (ggLinRefl_iff_isReflLin a).mp ha
  have ha_apply : ∀ v : V, a v = v - φ v • c := by
    intro v
    rw [haeq, Module.reflection_apply]
  obtain ⟨h₀, hh₀H, hh₀ne⟩ := hne
  have hφh₀_ne : φ h₀ ≠ 0 := by
    intro h0
    exact hh₀ne (by rw [ha_apply h₀, h0, zero_smul, sub_zero])
  have hc0 : c ≠ 0 := by
    intro hc
    exact QTwoLin.two_ne_zero_of_charP_three (K := ZMod 3) (by rw [← hφc, hc, map_zero])
  have hc_mem : (-(φ h₀)) • c ∈ H := by
    have hmem : a h₀ - h₀ ∈ H := H.sub_mem (hRH a haR h₀ hh₀H) hh₀H
    have hEq : a h₀ - h₀ = (-(φ h₀)) • c := by
      calc a h₀ - h₀ = (h₀ - φ h₀ • c) - h₀ := by rw [ha_apply h₀]
        _ = -(φ h₀ • c) := by abel
        _ = (-(φ h₀)) • c := (neg_smul (φ h₀) c).symm
    rwa [← hEq]
  have hcH : c ∈ H := by
    have ht : (-(φ h₀)) ≠ 0 := neg_ne_zero.mpr hφh₀_ne
    have h1 : ((-(φ h₀))⁻¹) • ((-(φ h₀)) • c) ∈ H := H.smul_mem _ hc_mem
    have h2 : ((-(φ h₀))⁻¹) • ((-(φ h₀)) • c) = c := inv_smul_smul₀ ht c
    rwa [h2] at h1
  let c' : ↥H := ⟨c, hcH⟩
  have hc'_ne : c' ≠ 0 := by
    intro h
    refine hc0 ?_
    simpa [c'] using congrArg (fun x : ↥H => (x : V)) h
  obtain ⟨b, hbRes, hbprop⟩ := ggQ2s08k11_res_mem_aux H R hRH a haR
  refine ⟨b, hbRes, hbprop, ?_⟩
  constructor
  · ext h
    rw [LinearEquiv.mul_apply, hbprop (b h), hbprop h]
    rw [← LinearEquiv.mul_apply, ha2]
    rfl
  · have hrange : ggLinMove b = ZMod 3 ∙ c' := by
      apply le_antisymm
      · intro v hv
        obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv
        have hv_eq : v = (-(φ (w : V))) • c' := by
          rw [← hw, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
          apply Subtype.ext
          change (b w : V) - (w : V) = (-(φ (w : V))) • (c : V)
          calc (b w : V) - (w : V) = (↑w - φ ↑w • c) - ↑w := by
                rw [hbprop w, ha_apply (w : V)]
            _ = -(φ (w : V) • c) := by abel
            _ = (-(φ (w : V))) • c := (neg_smul (φ (w : V)) c).symm
        exact Submodule.mem_span_singleton.mpr ⟨-(φ (w : V)), hv_eq.symm⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        let w₀ : ↥H := ⟨h₀, hh₀H⟩
        have hmem : b w₀ - w₀ ∈ ggLinMove b := by
          rw [ggLinMove]
          exact LinearMap.mem_range.mpr
            ⟨w₀, by rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]⟩
        have hval : b w₀ - w₀ = (-(φ (w₀ : V))) • c' := by
          apply Subtype.ext
          change (b w₀ : V) - (w₀ : V) = (-(φ (w₀ : V))) • (c : V)
          calc (b w₀ : V) - (w₀ : V) = (↑w₀ - φ ↑w₀ • c) - ↑w₀ := by
                rw [hbprop w₀, ha_apply (w₀ : V)]
            _ = -(φ (w₀ : V) • c) := by abel
            _ = (-(φ (w₀ : V))) • c := (neg_smul (φ (w₀ : V)) c).symm
        have ht : (-(φ (h₀ : V))) ≠ 0 := neg_ne_zero.mpr hφh₀_ne
        have hc'mem : c' ∈ ggLinMove b := by
          have hsplit : c' = (-(φ (w₀ : V)))⁻¹ • (b w₀ - w₀) := by
            rw [hval, smul_smul, inv_mul_cancel₀ ht, one_smul]
          rw [hsplit]
          exact Submodule.smul_mem _ _ hmem
        exact hc'mem
    rw [hrange]
    exact finrank_span_singleton hc'_ne

theorem ggQ2s08core_res_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H) (a : V ≃ₗ[ZMod 3] V)
      (haR : a ∈ R) :
    ∃ b ∈ GGQ2S08Res H R hRH, ∀ h : ↥H, ((b h : ↥H) : V) = a h := by
  exact ggQ2s08k11_res_mem_aux H R hRH a haR

end CFSG.StandardType

end
