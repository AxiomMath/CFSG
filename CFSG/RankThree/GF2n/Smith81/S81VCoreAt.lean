module

public import CFSG.RankThree.GF2n.Smith81.S81VCore

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K] [Finite K]
  {V : Type} [AddCommGroup V] [Module K V]

@[expose] def conjAct (A : SUid σ 6 →* (V ≃ₗ[K] V)) (g : SUid σ 6) : SUid σ 6 →* (V ≃ₗ[K] V) :=
  A.comp (MulAut.conj g).toMonoidHom

theorem conjAct_apply (A : SUid σ 6 →* (V ≃ₗ[K] V)) (g h : SUid σ 6) :
    conjAct A g h = A (g * h * g⁻¹) := rfl

theorem fixAt_conjAct (A : SUid σ 6 →* (V ≃ₗ[K] V)) (g : SUid σ 6) {W W' : Submodule F (Fin 6 → F)}
    (hW' : ∀ v, v ∈ W' ↔ ∃ w ∈ W, g • w = v) :
    fixAt σ (conjAct A g) W = fixAt σ A W' := by
  ext v
  rw [mem_fixAt, mem_fixAt, ptStab_conj g hW']
  constructor
  · intro h u hu
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hu
    exact h k hk
  · intro h k hk
    exact h _ (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hk)

theorem V1At_conjAct (A : SUid σ 6 →* (V ≃ₗ[K] V)) (β : V →ₗ[K] V →ₗ[K] K) (g : SUid σ 6)
    {W W' : Submodule F (Fin 6 → F)} (hW' : ∀ v, v ∈ W' ↔ ∃ w ∈ W, g • w = v) :
    V1At σ (conjAct A g) β W = V1At σ A β W' := by
  ext w
  rw [mem_V1At, mem_V1At, fixAt_conjAct A g hW', ptStab_conj g hW']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hu
    exact h2 k hk
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun k hk => h2 _ (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hk)⟩

theorem fixAt_map (A : SUid σ 6 →* (V ≃ₗ[K] V)) (h : SUid σ 6) {W W' : Submodule F (Fin 6 → F)}
    (hW' : ∀ v, v ∈ W' ↔ ∃ w ∈ W, h • w = v) :
    fixAt σ A W' = (fixAt σ A W).map (A h : V →ₗ[K] V) := by
  have h1 : fixAt σ A W' = fixAt σ (conjAct A h) W := (fixAt_conjAct A h hW').symm
  have key : ∀ (u : SUid σ 6) (v : V), A (h * u * h⁻¹) v = A h (A u ((A h).symm v)) := by
    intro u v
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [h1]
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨(A h).symm v, fun u hu => ?_, by simp⟩
    have h2 : A (h * u * h⁻¹) v = v := hv u hu
    rw [key] at h2
    apply (A h).injective
    rw [h2]
    simp
  · rintro ⟨w, hw, rfl⟩ u hu
    have hwu : A u w = w := hw u hu
    show A (h * u * h⁻¹) (A h w) = A h w
    rw [key]
    simp [hwu]

theorem core_main_U_at (hσ : IsUnitaryInvolution σ) (e₀ : K ≃+* Fσ σ) (hq : 4 ≤ Nat.card K)
    (hF : Nat.card F = Nat.card K ^ 2) (hV : finrank K V = 20) (A : SUid σ 6 →* (V ≃ₗ[K] V))
    (β : V →ₗ[K] V →ₗ[K] K) (hβalt : ∀ v, β v v = 0) (hβA : ∀ g u w, β (A g u) (A g w) = β u w)
    {W : Submodule F (Fin 6 → F)} (hW : IsPt σ W) (hline : finrank K (fixAt σ A W) = 1)
    (hspan : ⨆ g : SUid σ 6, (fixAt σ A W).map (A g : V →ₗ[K] V) = ⊤)
    (hV1 : finrank K (V1At σ A β W) ≤ 10) :
    ∃ (e' : K ≃+* Fσ σ) (ψ : V ≃ₗ[K] E3UWspace σ e') (g₁ : SUid σ 6),
      (∀ g v, ψ (A g v) = e3uWact σ e' g (ψ v)) ∧ (∀ v, v ∈ W ↔ ∃ w ∈ W₀ F, g₁ • w = v) ∧
        (fixAt σ A W).map (ψ : V →ₗ[K] E3UWspace σ e') =
          Submodule.span K {e3uWact σ e' g₁ (e3uP0 σ e')} := by
  classical
  obtain ⟨g₁, hg₁⟩ := exists_su_smul_W₀ hσ hW.1 hW.2
  have hfix : fixU σ (conjAct A g₁) = fixAt σ A W := fixAt_conjAct A g₁ hg₁
  have hV1' : V1U σ (conjAct A g₁) β = V1At σ A β W := V1At_conjAct A β g₁ hg₁
  have hspan' : ⨆ g : SUid σ 6, (fixU σ (conjAct A g₁)).map
      ((conjAct A g₁ g : V ≃ₗ[K] V) : V →ₗ[K] V) = ⊤ := by
    rw [hfix, ← hspan]
    exact Equiv.iSup_congr (MulAut.conj g₁).toEquiv (fun g => rfl)
  obtain ⟨e', ψ₀, hψ₀, hψ₀fix⟩ := core_main_U hσ e₀ hq hF hV (conjAct A g₁) β hβalt
    (fun g u w => hβA _ u w) (by rw [hfix]; exact hline) hspan' (by rw [hV1']; exact hV1)
  refine ⟨e', ψ₀.trans (e3uWact σ e' g₁), g₁, ?_, hg₁, ?_⟩
  · intro h v
    have h1 := hψ₀ (g₁⁻¹ * h * g₁) v
    have h2 : conjAct A g₁ (g₁⁻¹ * h * g₁) = A h := by
      rw [conjAct_apply]
      congr 1
      group
    rw [h2] at h1
    show e3uWact σ e' g₁ (ψ₀ (A h v)) = e3uWact σ e' h (e3uWact σ e' g₁ (ψ₀ v))
    rw [h1, ← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul]
    congr 2
    group
  · rw [← hfix, LinearEquiv.coe_trans, Submodule.map_comp, hψ₀fix, Submodule.map_span,
      Set.image_singleton]
    rfl

end CFSG.RankThree.GF2n.Smith81.S81V
