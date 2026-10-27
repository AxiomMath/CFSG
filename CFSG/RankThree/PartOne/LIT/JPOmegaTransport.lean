module

public import CFSG.RankThree.PartOne.LIT.JPOmega

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix CFSG.RankThree.SubgroupLists

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

@[expose] def glLin {K : Type*} [Field K] (g : GL (Fin 3) K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)
    (Matrix.GeneralLinearGroup.toLin g)

theorem glLin_apply {K : Type*} [Field K] (g : GL (Fin 3) K) (w : Fin 3 → K) :
    glLin g w = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w := rfl

theorem glLin_symm_apply {K : Type*} [Field K] (g : GL (Fin 3) K) (w : Fin 3 → K) :
    (glLin g⁻¹).symm w = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w := by
  rw [LinearEquiv.symm_apply_eq, glLin_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mulVec]

theorem jp_omega_of_card (hp : 7 ≤ p)
    (hcard : Nat.card (soGL (splitFormK (ZMod p))) = p * (p ^ 2 - 1))
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (B : Submodule (ZMod p) V)
    (M : Matrix (Fin 3) (Fin 3) (ZMod p)) (hM : Mᵀ = M) (hdet : M.det ≠ 0)
    (θ : B ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    (ρ : omegaGL M →* (V ≃ₗ[ZMod p] V))
    (hB : ∀ (y : omegaGL M) (b : B),
      ρ y (b : V) = ((θ.symm (((y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        θ b) : B) : V))
    (hq : ∀ (y : omegaGL M) (v : V), ρ y v - v ∈ B) (v₀ : V) :
    ∃ v : V, v - v₀ ∈ B ∧ ∀ y : omegaGL M, ρ y v = v := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g, c, hc, hgc⟩ := exists_congr_splitForm hp2 M hM hdet
  have hΩ : (omegaGL M).comap (MulAut.conj g : GL (Fin 3) (ZMod p) →* GL (Fin 3) (ZMod p)) =
      omegaGL (splitFormK (ZMod p)) := by
    rw [← omegaGL_smul (splitFormK (ZMod p)) hc, ← splitForm_eq, ← hgc, omegaGL_congr]
  have hmem : ∀ x : GL (Fin 3) (ZMod p), x ∈ omegaGL (splitFormK (ZMod p)) ↔
      g * x * g⁻¹ ∈ omegaGL M := fun x => by
    rw [← hΩ, Subgroup.mem_comap]
    rfl
  let Φ : omegaGL (splitFormK (ZMod p)) →* omegaGL M :=
    { toFun := fun x => ⟨g * x * g⁻¹, (hmem x).mp x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp [mul_assoc] }
  let θ₀ : B ≃ₗ[ZMod p] (Fin 3 → ZMod p) := θ.trans (glLin g⁻¹)
  have hθ₀ : ∀ w, θ₀.symm w = θ.symm ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w) := fun w => by
    rw [LinearEquiv.symm_trans_apply, glLin_symm_apply]
  have hθ₀' : ∀ b, θ₀ b = ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
      θ b := fun b => rfl
  obtain ⟨v, hvB, hv⟩ := jp_omega_standard hp hcard B θ₀ (ρ.comp Φ)
    (fun y b => by
      rw [MonoidHom.comp_apply, hB (Φ y) b, hθ₀, hθ₀', mulVec_mulVec, mulVec_mulVec]
      rfl)
    (fun y w => hq (Φ y) w) v₀
  refine ⟨v, hvB, fun y => ?_⟩
  have hy : g⁻¹ * (y : GL (Fin 3) (ZMod p)) * g ∈ omegaGL (splitFormK (ZMod p)) := by
    rw [hmem]
    have : g * (g⁻¹ * (y : GL (Fin 3) (ZMod p)) * g) * g⁻¹ = y := by group
    rw [this]
    exact y.2
  have := hv ⟨g⁻¹ * (y : GL (Fin 3) (ZMod p)) * g, hy⟩
  have e : Φ ⟨g⁻¹ * (y : GL (Fin 3) (ZMod p)) * g, hy⟩ = y := by
    apply Subtype.ext
    show g * (g⁻¹ * (y : GL (Fin 3) (ZMod p)) * g) * g⁻¹ = y
    group
  rwa [MonoidHom.comp_apply, e] at this

end CFSG.RankThree.PartOne.LIT
