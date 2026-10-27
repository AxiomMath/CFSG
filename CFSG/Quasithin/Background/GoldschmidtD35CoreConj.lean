module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreAct
public import CFSG.Quasithin.Background.GoldschmidtD35CoreSemi

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin Equiv
open scoped Matrix LinearAlgebra.Projectivization

variable {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
variable {pt : Fin 6 → ℙ K (Fin 3 → K)}

theorem exists_conj_aut (hval : IsValentiner K Γ) (hO : IsSixOrbit (valL Γ) pt)
    {n : gammaL K (Fin 3 → K)} {σ : Perm (Fin 6)} (hn : ∀ i, pointAct n (pt i) = pt (σ i)) :
    ∃ (β : Γ ≃* Γ) (Φ : (Fin 3 → K) ≃+ (Fin 3 → K)),
      (∀ γ : Γ, actPerm hO (β γ) = σ * actPerm hO γ * σ⁻¹) ∧
      ∀ (γ : Γ) (w : Fin 3 → K),
        Φ (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
          ((β γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ w := by
  have hD := threeQuaternaryData_of_valentiner hval
  have hex : ∀ γ : Γ, ∃ γ' : Γ, ∀ v, glLin γ'.1 v = n.1 (glLin γ.1 (n.1⁻¹ v)) := fun γ => by
    obtain ⟨g', hg', hv⟩ := hO.exists_conj_mem (Module.finrank_fin_fun K) hD.irreducible
      hD.scalar_mem hn (mem_valL γ)
    obtain ⟨γ', hγ', rfl⟩ := Subgroup.mem_map.1 hg'
    exact ⟨⟨γ', hγ'⟩, hv⟩
  choose β₀ hβ₀ using hex
  have hβ' : ∀ γ v, glLin (β₀ γ).1 (n.1 v) = n.1 (glLin γ.1 v) := fun γ v => by
    rw [hβ₀]
    simp
  have hext : ∀ γ γ' : Γ, (∀ v, glLin (β₀ γ).1 (n.1 v) = glLin γ'.1 (n.1 v)) → β₀ γ = γ' :=
    fun γ γ' h => Subtype.ext (glLin.injective (LinearEquiv.ext fun w => by
      obtain ⟨v, rfl⟩ := n.1.surjective w
      exact h v))
  have hmul : ∀ γ δ, β₀ (γ * δ) = β₀ γ * β₀ δ := fun γ δ => hext _ _ fun v => by
    rw [Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply, hβ', hβ', hβ']
    simp [map_mul]
  have hone : β₀ 1 = 1 := hext _ _ fun v => by
    rw [hβ']
    simp
  have hinj : Function.Injective β₀ := fun γ γ' h => by
    apply Subtype.ext
    apply glLin.injective
    refine LinearEquiv.ext fun v => n.1.injective ?_
    rw [← hβ', ← hβ', h]
  let β : Γ ≃* Γ := MulEquiv.ofBijective
    ({ toFun := β₀, map_one' := hone, map_mul' := hmul } : Γ →* Γ)
    (Finite.injective_iff_bijective.1 hinj)
  let Φ : (Fin 3 → K) ≃+ (Fin 3 → K) :=
    { toFun := n.1
      invFun := n.1.symm
      left_inv := n.1.symm_apply_apply
      right_inv := n.1.apply_symm_apply
      map_add' := n.2.1 }
  refine ⟨β, Φ, fun γ => ?_, fun γ w => ?_⟩
  · symm
    apply actPerm_unique
    intro i
    exact lineAction_conj_apply hn (actPerm_spec hO γ) (hβ₀ γ) i
  · show n.1 (_ *ᵥ w) = (β₀ γ).1 *ᵥ n.1 w
    rw [← glLin_apply, ← glLin_apply, hβ']

end CFSG.Quasithin.D35Core
