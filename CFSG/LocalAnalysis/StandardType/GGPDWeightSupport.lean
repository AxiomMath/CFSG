module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Matrix

theorem ggPD_weight_support {K : Type} [Field K] {d : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (ρ : Multiplicative (Fin 4 → ZMod 3) →* Matrix.GeneralLinearGroup (Fin d) K)
    (b : Module.Basis (Fin d) K (Fin d → K)) (u : Fin d → (Fin 4 → ZMod 3))
    (hb : ∀ (v : Multiplicative (Fin 4 → ZMod 3)) (j : Fin d),
      (ρ v : Matrix (Fin d) (Fin d) K).mulVec (b j) =
        ggPDChar ζ (u j ⬝ᵥ Multiplicative.toAdd v) • b j) :
    (∀ (w : Fin d → K), w ≠ 0 → ∀ ψ : Fin 4 → ZMod 3,
      (∀ v, (ρ v : Matrix (Fin d) (Fin d) K).mulVec w =
        ggPDChar ζ (ψ ⬝ᵥ Multiplicative.toAdd v) • w) → ψ ∈ Set.range u) ∧
    ((∀ v, ρ v ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K) → v = 1) →
      ∃ j, u j ≠ 0) ∧
    ((∃ z : Matrix.GeneralLinearGroup (Fin d) K, ∀ v, z * ρ v * z⁻¹ = ρ v⁻¹) →
      ∀ j, ∃ j', u j' = -u j) := by
  classical
  have hpart_a : ∀ (w : Fin d → K), w ≠ 0 → ∀ ψ : Fin 4 → ZMod 3,
      (∀ v, (ρ v : Matrix (Fin d) (Fin d) K).mulVec w =
        ggPDChar ζ (ψ ⬝ᵥ Multiplicative.toAdd v) • w) → ψ ∈ Set.range u := by
    intro w hw ψ hψ
    have hc : b.repr w ≠ 0 := by
      intro h0
      apply hw
      rw [← b.sum_repr w, h0]
      simp
    obtain ⟨j₀, hj₀⟩ := Finsupp.support_nonempty_iff.mpr hc
    have hcj₀ : b.repr w j₀ ≠ 0 := Finsupp.mem_support_iff.mp hj₀
    refine ⟨j₀, ?_⟩
    have hkey : ∀ v : Multiplicative (Fin 4 → ZMod 3),
        ggPDChar ζ (u j₀ ⬝ᵥ Multiplicative.toAdd v) =
          ggPDChar ζ (ψ ⬝ᵥ Multiplicative.toAdd v) := by
      intro v
      have hmat : (LinearMap.toMatrix b b
          (Matrix.mulVecLin ((ρ v) : Matrix (Fin d) (Fin d) K))).mulVec
          (fun j => b.repr w j) =
          fun j => ggPDChar ζ (ψ ⬝ᵥ Multiplicative.toAdd v) * b.repr w j := by
        rw [LinearMap.toMatrix_mulVec_repr]
        have hTw : Matrix.mulVecLin ((ρ v) : Matrix (Fin d) (Fin d) K) w =
            ggPDChar ζ (ψ ⬝ᵥ Multiplicative.toAdd v) • w := by
          rw [Matrix.mulVecLin_apply]
          exact hψ v
        rw [hTw, map_smul]
        ext j
        rw [Finsupp.smul_apply, smul_eq_mul]
      have hdiag : LinearMap.toMatrix b b
          (Matrix.mulVecLin ((ρ v) : Matrix (Fin d) (Fin d) K)) =
          Matrix.diagonal (fun j => ggPDChar ζ (u j ⬝ᵥ Multiplicative.toAdd v)) := by
        ext i j
        rw [LinearMap.toMatrix_apply, Matrix.mulVecLin_apply, hb v j]
        by_cases hij : i = j
        · subst hij
          simp [map_smul, b.repr_self, Finsupp.single_eq_same, smul_eq_mul]
        · simp [map_smul, b.repr_self, hij, smul_eq_mul]
      rw [hdiag] at hmat
      have hcoord := congrFun hmat j₀
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j₀] at hcoord
      · rw [Matrix.diagonal_apply, if_pos rfl] at hcoord
        exact mul_right_cancel₀ hcj₀ hcoord
      · intro k _ hk
        rw [Matrix.diagonal_apply, if_neg (Ne.symm hk), zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ j₀) hmem
    funext k
    have hk := hkey (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3)))
    change ggPDChar ζ (u j₀ ⬝ᵥ (Pi.single k (1 : ZMod 3) : Fin 4 → ZMod 3)) =
      ggPDChar ζ (ψ ⬝ᵥ (Pi.single k (1 : ZMod 3) : Fin 4 → ZMod 3)) at hk
    rw [dotProduct_single, mul_one, dotProduct_single, mul_one] at hk
    simp only [ggPDChar] at hk
    exact ZMod.val_injective 3 (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hk)
  refine ⟨hpart_a, ?_, ?_⟩
  · intro hvc
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hfix : ∀ v : Multiplicative (Fin 4 → ZMod 3), ρ v = 1 := by
      intro v
      apply Units.ext
      apply Matrix.toLin'.injective
      apply b.ext
      intro j
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hb v j, hall j]
      simp [Units.val_one, Matrix.one_mulVec, ggPDChar]
    have hcontr : Multiplicative.ofAdd
        (Pi.single (0 : Fin 4) (1 : ZMod 3) : Fin 4 → ZMod 3) = 1 := by
      apply hvc
      rw [hfix]
      exact Subgroup.one_mem _
    have hsingle : (Pi.single (0 : Fin 4) (1 : ZMod 3) : Fin 4 → ZMod 3) = 0 := by
      have h := congrArg Multiplicative.toAdd hcontr
      exact h
    have h10 : (1 : ZMod 3) = 0 := by simpa using congrFun hsingle 0
    exact one_ne_zero h10
  · rintro ⟨z, hz⟩ j
    have hzj : (z : Matrix (Fin d) (Fin d) K).mulVec (b j) ≠ 0 := by
      intro h0
      have hinj : Function.Injective (z : Matrix (Fin d) (Fin d) K).mulVec :=
        Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit z)
      exact b.ne_zero j (hinj (by rw [h0, Matrix.mulVec_zero]))
    have hev : ∀ v : Multiplicative (Fin 4 → ZMod 3),
        (ρ v : Matrix (Fin d) (Fin d) K) *ᵥ ((z : Matrix (Fin d) (Fin d) K) *ᵥ b j) =
        ggPDChar ζ ((-u j) ⬝ᵥ Multiplicative.toAdd v) •
          ((z : Matrix (Fin d) (Fin d) K) *ᵥ b j) := by
      intro v
      have hzv_gl : (ρ v * z : Matrix.GeneralLinearGroup (Fin d) K) = z * ρ (v⁻¹) := by
        have h0 := hz (v⁻¹)
        have h1 : ρ ((v⁻¹)⁻¹) = ρ v := congrArg ρ (inv_inv v)
        have h3 : ρ (v⁻¹) = (ρ v)⁻¹ := map_inv ρ v
        have h : z * (ρ v)⁻¹ * z⁻¹ = ρ v := by
          calc z * (ρ v)⁻¹ * z⁻¹
              = z * ρ (v⁻¹) * z⁻¹ := by rw [h3]
            _ = ρ ((v⁻¹)⁻¹) := h0
            _ = ρ v := h1
        rw [← h, ← h3]
        group
      calc (ρ v : Matrix (Fin d) (Fin d) K) *ᵥ ((z : Matrix (Fin d) (Fin d) K) *ᵥ b j)
          = ((ρ v * z : Matrix.GeneralLinearGroup (Fin d) K) :
              Matrix (Fin d) (Fin d) K) *ᵥ b j := by
            rw [Units.val_mul, Matrix.mulVec_mulVec]
        _ = ((z * ρ (v⁻¹) : Matrix.GeneralLinearGroup (Fin d) K) :
              Matrix (Fin d) (Fin d) K) *ᵥ b j := by rw [hzv_gl]
        _ = (z : Matrix (Fin d) (Fin d) K) *ᵥ
              ((ρ (v⁻¹) : Matrix (Fin d) (Fin d) K) *ᵥ b j) := by
            rw [Units.val_mul, Matrix.mulVec_mulVec]
        _ = (z : Matrix (Fin d) (Fin d) K) *ᵥ
              (ggPDChar ζ (u j ⬝ᵥ Multiplicative.toAdd (v⁻¹)) • b j) := by
            rw [hb (v⁻¹) j]
        _ = ggPDChar ζ (u j ⬝ᵥ Multiplicative.toAdd (v⁻¹)) •
              ((z : Matrix (Fin d) (Fin d) K) *ᵥ b j) := by rw [Matrix.mulVec_smul]
        _ = ggPDChar ζ ((-u j) ⬝ᵥ Multiplicative.toAdd v) •
              ((z : Matrix (Fin d) (Fin d) K) *ᵥ b j) := by
            have harg : u j ⬝ᵥ Multiplicative.toAdd (v⁻¹) =
                (-u j) ⬝ᵥ Multiplicative.toAdd v := by
              rw [show Multiplicative.toAdd (v⁻¹) = -Multiplicative.toAdd v from rfl]
              exact (dotProduct_neg (u j) (Multiplicative.toAdd v)).trans
                (neg_dotProduct (u j) (Multiplicative.toAdd v)).symm
            rw [harg]
    obtain ⟨j', hj'⟩ := hpart_a ((z : Matrix (Fin d) (Fin d) K) *ᵥ b j) hzj (-u j) hev
    exact ⟨j', hj'⟩

end CFSG.StandardType

end
