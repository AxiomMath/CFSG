module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Fact
public import Certificates.Certificate7099

public section

namespace CFSG.Quasithin.G112A2

open Module CFSG.Open CFSG.Quasithin.H13.A7Mod


variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem g112ConclA2_concl4 (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V) (W : Submodule (ZMod 2) V)
    (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (hH : G111Hyp B Γ v₁ W X X₀) (h4 : G112Concl4 Γ) :
    ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
      v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  classical
  intro t ht hr _ ha2
  exfalso
  obtain ⟨-, φ, ψ, hψ⟩ := h4
  set c := conjEquiv ψ with hcdef
  set F := (genFittingFStar ↥Γ).map Γ.subtype with hFdef
  have hcF : ∀ γ : ↥(genFittingFStar ↥Γ),
      c ((γ : ↥Γ) : V ≃ₗ[ZMod 2] V) = pAct (φ γ : Equiv.Perm (Fin 7)) := by
    intro γ
    refine LinearEquiv.ext fun x => Subtype.ext ?_
    rw [conjEquiv_apply]
    have h1 := hψ γ (ψ.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1
  have hpA7 : pA7 = F.map c.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨γ, hγ⟩ := φ.surjective ⟨σ, hσ⟩
      refine ⟨((γ : ↥Γ) : V ≃ₗ[ZMod 2] V), ⟨γ, γ.2, rfl⟩, ?_⟩
      show c _ = pAct σ
      rw [hcF, hγ]
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      exact ⟨φ ⟨γ, hγ⟩, (φ ⟨γ, hγ⟩).2, (hcF ⟨γ, hγ⟩).symm⟩
  have hΓF : Γ ≤ Subgroup.normalizer (F : Set (V ≃ₗ[ZMod 2] V)) := by
    have := genFittingFStar_normal' ↥Γ
    have h1 := Subgroup.le_normalizer_map (H := genFittingFStar ↥Γ) Γ.subtype
    rw [Subgroup.normalizer_eq_top (genFittingFStar ↥Γ), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  have htN : c t ∈ Subgroup.normalizer (pA7 : Set (V7 ≃ₗ[ZMod 2] V7)) := by
    rw [hpA7]
    exact Subgroup.le_normalizer_map c.toMonoidHom ⟨t, hΓF (hH.X_le ht), rfl⟩
  obtain ⟨π, hπ⟩ := eq_pAct_of_mem_normalizer
    (stabCount_of_raw Certificates.certificate7099) htN
  let B' : LinearMap.BilinForm (ZMod 2) V7 :=
    B.compl₁₂ ψ.symm.toLinearMap ψ.symm.toLinearMap
  have hB' : ∀ x y, B' x y = B (ψ.symm x) (ψ.symm y) := fun _ _ => rfl
  have hB0 : B' = B0 := by
    refine eq_B0 B' (fun x => by rw [hB']; exact hH.alt _) (fun x hx => ?_) ?_
    · have h0 : ψ.symm x = 0 := hH.nondegenerate _ fun w => by
        have := hx (ψ w)
        rwa [hB', LinearEquiv.symm_apply_apply] at this
      simpa using congrArg ψ h0
    · intro σ hσ x y
      obtain ⟨γ, hγ⟩ := φ.surjective ⟨σ, hσ⟩
      have hc : pAct σ = c ((γ : ↥Γ) : V ≃ₗ[ZMod 2] V) := by rw [hcF, hγ]
      rw [hc, hB', hB', conjEquiv_apply, conjEquiv_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply]
      exact hH.isometry _ (γ : ↥Γ).2 _ _
  have hπ1 : ∀ p, π p = p := by
    intro p
    by_contra hp
    have h1 : B' (f p) (c t (f p)) = 0 := by
      rw [hB', conjEquiv_apply, LinearEquiv.symm_apply_apply]
      exact ha2 _
    rw [hπ, pAct_f, hB0, B0_f, if_neg (Ne.symm hp)] at h1
    exact one_ne_zero h1
  have ht1 : t = 1 := by
    have hπ' : π = 1 := Equiv.ext hπ1
    apply c.injective
    rw [hπ, hπ', map_one, map_one]
  rw [ht1] at hr
  have h0 : ((1 : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id) = 0 := by
    ext v
    simp
  rw [h0, LinearMap.range_zero, finrank_bot] at hr
  exact absurd hr (by norm_num)

end CFSG.Quasithin.G112A2
