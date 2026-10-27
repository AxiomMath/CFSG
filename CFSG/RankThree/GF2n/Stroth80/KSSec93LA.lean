module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalarsPlusTwo
import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaFacts
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport

public section

namespace CFSG.RankThree.GF2n.Stroth80.KS93

open Module QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Matrix

section Singular

private theorem exists_mem_ne_zero_coord_eq_zero {K : Type} [Field K]
    {U : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h3 : 3 ≤ finrank K U) (c : Fin 2 → Fin 2 ⊕ Fin 2) :
    ∃ p ∈ U, p ≠ 0 ∧ ∀ j, p (c j) = 0 := by
  let f : U →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi fun j => (LinearMap.proj (c j) : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K).comp U.subtype
  have hlt : finrank K (Fin 2 → K) < finrank K U := by
    rw [Module.finrank_fin_fun]
    omega
  obtain ⟨x, hx, hx0⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), fun j => congrFun (LinearMap.mem_ker.mp hx) j⟩

theorem eq_bot_of_singular {K : Type} [Field K] [Finite K] [CharP K 2]
    {U Y : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hYU : Y ≤ U)
    (hperp : ∀ y ∈ Y, ∀ u ∈ U, polar (quadPlus 2 K) y u = 0)
    (hdim : finrank K Y + finrank K U = 4)
    (hpt : ∀ p ∈ U, p ≠ 0 → quadPlus 2 K p = 0 → ∀ y ∈ Y, ∃ c : K, y = c • p) :
    Y = ⊥ := by
  by_cases h3 : 3 ≤ finrank K U
  · obtain ⟨p₁, hp₁U, hp₁0, hp₁⟩ := exists_mem_ne_zero_coord_eq_zero h3 Sum.inr
    obtain ⟨p₂, hp₂U, hp₂0, hp₂⟩ := exists_mem_ne_zero_coord_eq_zero h3 Sum.inl
    refine (Submodule.eq_bot_iff Y).mpr fun y hy => ?_
    obtain ⟨c₁, hc₁⟩ := hpt p₁ hp₁U hp₁0 (by simp [quadPlus_apply, hp₁]) y hy
    obtain ⟨c₂, hc₂⟩ := hpt p₂ hp₂U hp₂0 (by simp [quadPlus_apply, hp₂]) y hy
    funext x
    rcases x with j | j
    · rw [hc₂]
      simp [hp₂]
    · rw [hc₁]
      simp [hp₁]
  · exfalso
    have hYle : finrank K Y ≤ finrank K U := Submodule.finrank_mono hYU
    have hU2 : finrank K U = 2 := by omega
    have hYeq : Y = U := Submodule.eq_of_le_of_finrank_eq hYU (by omega)
    have hmemY : ∀ y ∈ U, y ∈ Y := fun y hy => by rw [hYeq]; exact hy
    obtain ⟨u₁, hu₁U, hu₁0⟩ : ∃ u ∈ U, u ≠ 0 := by
      obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K U)
      exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
    obtain ⟨u₂, hu₂U, hu₂⟩ : ∃ u ∈ U, u ∉ Submodule.span K {u₁} := by
      by_contra hcon
      push Not at hcon
      have hle := Submodule.finrank_mono (show U ≤ Submodule.span K {u₁} from hcon)
      rw [finrank_span_singleton hu₁0] at hle
      omega
    obtain ⟨p, hpU, hp0, hpQ⟩ : ∃ p ∈ U, p ≠ 0 ∧ quadPlus 2 K p = 0 := by
      by_cases hq : quadPlus 2 K u₁ = 0
      · exact ⟨u₁, hu₁U, hu₁0, hq⟩
      · obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (quadPlus 2 K u₂ / quadPlus 2 K u₁)
        have hμ' : quadPlus 2 K u₂ = μ * μ * quadPlus 2 K u₁ := (div_eq_iff hq).mp hμ
        refine ⟨u₂ + μ • u₁, U.add_mem hu₂U (U.smul_mem μ hu₁U), fun h => hu₂ ?_, ?_⟩
        · have h' : u₂ = (-μ) • u₁ := by
            rw [neg_smul, eq_neg_iff_add_eq_zero]
            exact h
          rw [h']
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u₁)
        · have hpol : polar (quadPlus 2 K) u₂ (μ • u₁) = 0 := by
            rw [polar_smul_right_eq, hperp u₂ (hmemY u₂ hu₂U) u₁ hu₁U, mul_zero]
          have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
          rw [QuadraticMap.map_add (quadPlus 2 K), map_smul_eq_sq, hpol]
          linear_combination (quadPlus 2 K u₂) * h2 - hμ'
    have hle : U ≤ Submodule.span K {p} := fun y hy => by
      obtain ⟨c, hc⟩ := hpt p hpU hp0 hpQ y (hmemY y hy)
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hp0] at this
    omega

end Singular

section Schur

theorem exists_eq_smul_polar {K : Type} [Field K] [Finite K] (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1)
    (E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)))
    {Γ : Type*} [Group Γ] (φ : Γ →* GL (Fin 2 ⊕ Fin 2) K)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 2 K))
    {W : Type*} [AddCommGroup W] (act : Γ → W →+ W)
    (κ : W →+ (Fin 2 ⊕ Fin 2 → K)) (hκ : Function.Surjective κ)
    (hκact : ∀ g w, κ (act g w) = (φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ κ w)
    (P : W →+ ((Fin 2 ⊕ Fin 2 → K) →ₗ[K] K))
    (hPact : ∀ g w b, P (act g w) ((φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ b) = P w b)
    (hPker : ∀ w, κ w = 0 → P w = 0) :
    ∃ c : K, ∀ w b, P w b = c * polar (quadPlus 2 K) (κ w) b := by
  have hnd : (polarBilin (quadPlus 2 K)).Nondegenerate := nondegenerate_polarBilin_quadPlus 2 K
  have hPeq : ∀ w w', κ w = κ w' → P w = P w' := fun w w' h => by
    have h0 := hPker (w - w') (by rw [map_sub, h, sub_self])
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  obtain ⟨σ, hσ⟩ : ∃ σ : (Fin 2 ⊕ Fin 2 → K) → W, ∀ a, κ (σ a) = a :=
    ⟨Function.surjInv hκ, Function.surjInv_eq hκ⟩
  obtain ⟨A, hA⟩ : ∃ A : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K),
      ∀ a b, polar (quadPlus 2 K) (A a) b = P (σ a) b := by
    refine ⟨AddMonoidHom.mk'
      (fun a => (LinearMap.BilinForm.toDual (polarBilin (quadPlus 2 K)) hnd).symm (P (σ a)))
        fun a a' => ?_,
      fun a b => ?_⟩
    · have h : P (σ (a + a')) = P (σ a) + P (σ a') := by
        rw [← map_add]
        exact hPeq _ _ (by rw [hσ, map_add, hσ, hσ])
      simp only [h, map_add]
    · have h := LinearMap.BilinForm.apply_toDual_symm_apply (B := polarBilin (quadPlus 2 K))
        (hB := hnd) (P (σ a)) b
      rwa [polarBilin_apply_apply] at h
  have key : ∀ x y : Fin 2 ⊕ Fin 2 → K,
      (∀ b, polar (quadPlus 2 K) x b = polar (quadPlus 2 K) y b) → x = y := fun x y h => by
    refine sub_eq_zero.mp (eq_zero_of_polar_eq_zero hnd fun b => ?_)
    rw [QuadraticMap.polar_sub_left, h b, sub_self]
  have hcomm : ∀ M ∈ StatedOmega (StatedQuadPlus 2 K), ∀ v,
      A ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ A v := by
    intro M hM a
    obtain ⟨g, rfl⟩ : M ∈ φ.range := by rw [hφ]; exact hM
    refine key _ _ fun b => ?_
    have hgg : (φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((φ g)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hinv : (φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        ((((φ g)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ b) =
          b := by
      rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
    have hσg : P (σ ((φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a)) =
        P (act g (σ a)) :=
      hPeq _ _ (by rw [hσ, hκact, hσ])
    have h1 := hPact g (σ a)
      ((((φ g)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ b)
    have h2 := E.polar_mulVec hM (A a)
      ((((φ g)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ b)
    rw [hinv] at h1 h2
    rw [hA, hσg, h1, ← hA]
    exact h2.symm
  obtain ⟨c, hc⟩ := addCommutantScalar_statedOmegaPlus_two hK A hcomm
  refine ⟨c, fun w b => ?_⟩
  calc P w b = P (σ (κ w)) b := by rw [hPeq w (σ (κ w)) (by rw [hσ])]
    _ = polar (quadPlus 2 K) (A (κ w)) b := (hA _ _).symm
    _ = polar (quadPlus 2 K) (c • κ w) b := by rw [hc]
    _ = c * polar (quadPlus 2 K) (κ w) b := polar_smul_left_eq _ c _ _

end Schur

end CFSG.RankThree.GF2n.Stroth80.KS93
