module

public import CFSG.LocalAnalysis.StandardType.GGQTwoThmA
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoConnectivity
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2x_eq_one_or_neg_one (a : ZMod 3) (ha : a ≠ 0) : a = 1 ∨ a = -1 :=
  (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1) a ha

private lemma ggQ2x_sq_eq_one (a : ZMod 3) (ha : a ≠ 0) : a * a = 1 :=
  (by decide : ∀ a : ZMod 3, a ≠ 0 → a * a = 1) a ha

private lemma ggQ2x_rootPair_self (D : GGQ2Lin 3) (γ : ↥D.rootPairs) :
    γ.1.1 γ.1.2 = 2 := by
  obtain ⟨k, w, _, hq2, hq1⟩ := γ.2
  rw [hq2, hq1]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply, D.root_coroot_self]

private lemma ggQ2x_simplePair_mem (D : GGQ2Lin 3) (k : D.ι) :
    (D.root k, D.coroot k) ∈ D.rootPairs :=
  ⟨k, 1, D.weyl.one_mem, rfl, by
    change D.root k = (D.root k).comp (LinearMap.id : D.V →ₗ[ZMod 3] D.V)
    rw [LinearMap.comp_id]⟩

private lemma ggQ2x_simpleRefl_mem_weyl (D : GGQ2Lin 3) (k : D.ι) :
    D.simpleRefl k ∈ D.weyl :=
  Subgroup.subset_closure ⟨k, trivial, rfl⟩

private lemma ggQ2x_rootRefl_mem_weyl (D : GGQ2Lin 3) (γ : ↥D.rootPairs) :
    Module.reflection (ggQ2x_rootPair_self D γ) ∈ D.weyl := by
  obtain ⟨k, w, hw, hq2, hq1⟩ := γ.2
  have heq : Module.reflection (ggQ2x_rootPair_self D γ) = w * D.simpleRefl k * w.symm := by
    ext v
    rw [Module.reflection_apply v (ggQ2x_rootPair_self D γ),
      LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl,
      Module.reflection_apply (w.symm v) (D.root_coroot_self k)]
    rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rw [hq1, hq2]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (ggQ2x_simpleRefl_mem_weyl D k))
    (Subgroup.inv_mem _ hw)

theorem ggQ2_refl_orthogonal {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hbas : D.Basis)
    (h4 : 4 ≤ Fintype.card D.ι) (β : LinearMap.BilinForm (ZMod p) D.V) (hβ : β.IsSymm)
    (d : ↥D.rootPairs → ZMod p) (hd : ∀ γ, d γ ≠ 0)
    (hβh : ∀ γ v, β γ.1.2 v = d γ * γ.1.1 v)
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    {c : D.V} {φ : Module.Dual (ZMod p) D.V} (hφ : φ c = 2) (ht : Module.reflection hφ ∈ A) :
    ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * β c v := by
  subst hp
  classical
  by_cases hc : ∃ γ : ↥D.rootPairs, c ∈ Submodule.span (ZMod 3) ({γ.1.2} : Set D.V)
  ·
    obtain ⟨γ, hcγ⟩ := hc
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hcγ
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hφ
      exact two_ne_zero_of_charP_three (K := ZMod 3) hφ.symm
    have hk0 : k ≠ 0 := by
      intro h0
      exact hc0 (by rw [← hk, h0, zero_smul])
    have hα : γ.1.1 γ.1.2 = 2 := ggQ2x_rootPair_self D γ
    have hφ' : (k⁻¹ • γ.1.1) c = 2 := by
      rw [← hk, LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hα,
        ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
    by_cases hphi : φ = k⁻¹ • γ.1.1
    ·
      subst hphi
      refine ⟨(d γ)⁻¹, ggQ2x_eq_one_or_neg_one _ (inv_ne_zero (hd γ)), ?_⟩
      intro v
      have hβcv : β c v = k * (d γ * γ.1.1 v) := by
        rw [← hk, LinearMap.BilinForm.smul_left, hβh γ v]
      have hksq : k * k = 1 := ggQ2x_sq_eq_one k hk0
      have hkinv : k⁻¹ = k := by
        apply mul_right_cancel₀ hk0
        rw [inv_mul_cancel₀ hk0, hksq]
      have hεeq : (d γ)⁻¹ * (k * d γ) = k := by
        rw [show (d γ)⁻¹ * (k * d γ) = k * ((d γ)⁻¹ * d γ) from by ring,
          inv_mul_cancel₀ (hd γ), mul_one]
      rw [LinearMap.smul_apply, smul_eq_mul, hkinv, hβcv]
      calc k * γ.1.1 v
          = ((d γ)⁻¹ * (k * d γ)) * γ.1.1 v := by rw [hεeq]
        _ = (d γ)⁻¹ * ((k * d γ) * γ.1.1 v) := by rw [mul_assoc]
        _ = (d γ)⁻¹ * (k * (d γ * γ.1.1 v)) := by ring
    ·
      exfalso
      have hφ'_mem : Module.reflection hφ' ∈ A := by
        have heq : Module.reflection hφ' = Module.reflection (ggQ2x_rootPair_self D γ) := by
          ext z
          rw [Module.reflection_apply z hφ',
            Module.reflection_apply z (ggQ2x_rootPair_self D γ)]
          rw [← hk, LinearMap.smul_apply, smul_eq_mul, smul_smul]
          have hs : (k⁻¹ * γ.1.1 z) * k = γ.1.1 z := by
            rw [mul_assoc, mul_comm (γ.1.1 z) k, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
          rw [hs]
        rw [heq]
        exact hW (ggQ2x_rootRefl_mem_weyl D γ)
      have htv : IsTransvectionLin (Module.reflection hφ' * Module.reflection hφ) :=
        transvection_of_same_centre hφ hφ' hphi
      exact hTF _ (Subgroup.mul_mem _ hφ'_mem ht) htv
  ·
    push Not at hc
    haveI : Nonempty D.ι := Fintype.card_pos_iff.mp (by omega)
    have hspan : Submodule.span (ZMod 3) (Set.range D.coroot) = ⊤ :=
      hbas.1.span_eq_top_of_card_eq_finrank hbas.2
    let sp : D.ι → ↥D.rootPairs := fun k => ⟨(D.root k, D.coroot k), ggQ2x_simplePair_mem D k⟩
    have hspan' : Submodule.span (ZMod 3) (Set.range (fun γ : ↥D.rootPairs => γ.1.2)) = ⊤ := by
      rw [eq_top_iff, ← hspan]
      refine Submodule.span_mono ?_
      rintro z ⟨i, rfl⟩
      exact ⟨sp i, rfl⟩
    have hβsymm : LinearMap.IsSymm β := ⟨fun u w => hβ.eq u w⟩
    exact refl_eq_orthogonal (V := D.V) (ι := ↥D.rootPairs)
      (fun γ : ↥D.rootPairs => γ.1.2) (fun γ : ↥D.rootPairs => γ.1.1)
      (fun γ => ggQ2x_rootPair_self D γ) β hβsymm d hd hβh hspan'
      A hTF (fun γ => hW (ggQ2x_rootRefl_mem_weyl D γ))
      hφ ht hc (ggQ2_connectivity (p := 3) rfl D hbas h4 c)

end CFSG.StandardType

end
