module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.F918XV8aCount
public import CFSG.Quasithin.Background.F918XV8aReal
public import CFSG.Quasithin.Background.GoldschmidtD35CoreConj
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.GoldschmidtD35CoreReal
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin Matrix

theorem exists_perm_family {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (hval : IsValentiner K Γ) :
    ∃ (θ : Equiv.Perm (Fin 6) → MulAut ↥Γ)
      (Φ : Equiv.Perm (Fin 6) → ((Fin 3 → K) ≃+ (Fin 3 → K))),
      Function.Injective θ ∧ ∀ (σ : Equiv.Perm (Fin 6)) (γ : ↥Γ) (w : Fin 3 → K),
        Φ σ ((((γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
          (((θ σ γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            Φ σ w := by
  classical
  obtain ⟨pt, hO⟩ := D35Core.exists_isSixOrbit (D35Core.threeQuaternaryData_of_valentiner hval)
  have hex : ∀ σ : Equiv.Perm (Fin 6), ∃ (β : ↥Γ ≃* ↥Γ) (Φ : (Fin 3 → K) ≃+ (Fin 3 → K)),
      (∀ γ : ↥Γ, D35Core.actPerm hO (β γ) = σ * D35Core.actPerm hO γ * σ⁻¹) ∧
      ∀ (γ : ↥Γ) (w : Fin 3 → K),
        Φ ((((γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
          (((β γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            Φ w := by
    intro σ
    obtain ⟨n, hn⟩ := hO.exists_induces hval.1 (Module.finrank_fin_fun K)
      (D35Core.threeQuaternaryData_of_valentiner hval).irreducible σ
    exact D35Core.exists_conj_aut hval hO hn
  choose β Φ hβ hΦ using hex
  refine ⟨β, Φ, fun σ σ' h => ?_, hΦ⟩
  apply SteinbergCB.conjPerm_injective (n := 6) (by norm_num)
  refine MulEquiv.ext fun x => ?_
  obtain ⟨γ, rfl⟩ := D35Core.actHom_surjective hO x
  apply Subtype.ext
  rw [SteinbergCB.conjPerm_apply, SteinbergCB.conjPerm_apply, D35Core.coe_actHom,
    ← hβ σ γ, ← hβ σ' γ, h]

theorem case8Twist_holds : Case8Twist := by
  intro V _ _ _ G L A _ h8
  obtain ⟨-, -, -, K, _, _, Γ₀, hK4, hdet, hhat, hcen, π, hπ, -⟩ := h8
  have hval : IsValentiner K Γ₀ := ⟨hK4, hdet, hhat, hcen⟩
  have hinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful Γ₀)
  let e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hhatL : IsHat ↥L ↥(alternatingGroup (Fin 6)) := IsHat.of_mulEquiv e hhat
  have : Finite (MulAut V) := MulEquiv.finite_left
  have : Finite ↥L := inferInstance
  have : Finite (MulAut ↥L) := MulEquiv.finite_left
  refine ⟨?_, Or.inr (Or.inr ⟨hhatL.2.1, hhatL.2.2⟩)⟩
  obtain ⟨θ, Φ, hθ, hΦ⟩ := exists_perm_family hval
  have hα : ∀ (σ : Equiv.Perm (Fin 6)) (γ : ↥Γ₀),
      MulAut.congr e (θ σ) (π γ) = π (θ σ γ) := fun σ γ => by
    rw [MulAut.congr_apply]
    show e (θ σ (e.symm (e γ))) = e (θ σ γ)
    rw [MulEquiv.symm_apply_apply]
  refine twoClassMod_of_perm_family (card_mulAut_le_of_isHat hhatL)
    (fun σ => MulAut.congr e (θ σ)) (fun σ σ' h => hθ ?_) fun σ => ?_
  · refine MulEquiv.ext fun γ => hinj ?_
    rw [← hα σ γ, ← hα σ' γ]
    exact congrArg (fun α : MulAut ↥L => α (π γ)) h
  · exact mem_realized_of_additive hπ (MulAut.congr e (θ σ)) (θ σ) (hα σ) (Φ σ) (hΦ σ)

end CFSG.Quasithin.F918X
