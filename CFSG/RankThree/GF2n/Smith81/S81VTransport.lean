module

public import CFSG.RankThree.GF2n.Smith81.S81UModelData

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.GF2n.Smith81.U6Cube

section Transport

variable {G : Type} [Group G] {M Q Z B : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {X : Type} [AddCommGroup X] [Module K X]

@[expose] def transportU (ψ : M₀.E ≃ₗ[K] X) (T : M₀.E ≃ₗ[K] M₀.E) : X ≃ₗ[K] X :=
  ψ.symm.trans (T.trans ψ)

theorem transportU_apply (ψ : M₀.E ≃ₗ[K] X) (T : M₀.E ≃ₗ[K] M₀.E) (e : M₀.E) :
    transportU ψ T (ψ e) = ψ (T e) := by
  simp [transportU]

theorem transportU_mul (ψ : M₀.E ≃ₗ[K] X) (T₁ T₂ : M₀.E ≃ₗ[K] M₀.E) :
    transportU ψ (T₁ * T₂) = transportU ψ T₁ * transportU ψ T₂ := by
  ext ξ
  simp [transportU]

theorem transportU_one (ψ : M₀.E ≃ₗ[K] X) : transportU ψ (1 : M₀.E ≃ₗ[K] M₀.E) = 1 := by
  ext ξ
  simp [transportU]

theorem transportU_injective (ψ : M₀.E ≃ₗ[K] X) :
    Function.Injective (transportU ψ : (M₀.E ≃ₗ[K] M₀.E) → (X ≃ₗ[K] X)) := by
  intro T₁ T₂ h
  ext e
  have := congrArg (fun S : X ≃ₗ[K] X => S (ψ e)) h
  simp only [transportU_apply] at this
  exact ψ.injective this

theorem transportU_of_equivariant {Γ : Type} [Group Γ] (ρ : Γ →* (X ≃ₗ[K] X))
    (A : Γ →* (M₀.E ≃ₗ[K] M₀.E)) (ψ : M₀.E ≃ₗ[K] X) (hψA : ∀ g v, ψ (A g v) = ρ g (ψ v))
    (g : Γ) : transportU ψ (A g) = ρ g := by
  apply LinearEquiv.ext
  intro ξ
  obtain ⟨v, rfl⟩ := ψ.surjective ξ
  rw [transportU_apply, hψA]

end Transport

section Phi

variable {G : Type} [Group G] {M Q Z B : Subgroup G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

theorem exists_phiU (e' : K ≃+* Fσ σ) (ψ : M₀.E ≃ₗ[K] E3UWspace σ e')
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hTker : ∀ s : Lgen M (LB M Q B), T s = 1 ↔ (s : G) ∈ Q)
    (A : SUid σ 6 →* (M₀.E ≃ₗ[K] M₀.E))
    (hψA : ∀ g v, ψ (A g v) = e3uWact σ e' g (ψ v))
    (hAT1 : ∀ s : Lgen M (LB M Q B), ∃ h : SUid σ 6, ∀ v, T s v = A h v)
    (hAT2 : ∀ h : SUid σ 6, ∃ s : Lgen M (LB M Q B), ∀ v, T s v = A h v) :
    ∃ φ : Lgen M (LB M Q B) →* (E3UWspace σ e' ≃ₗ[K] E3UWspace σ e'),
      (∀ s, φ s = transportU ψ (T s)) ∧ φ.range = e3uGam σ e' ∧
        (∀ s : Lgen M (LB M Q B), φ s = 1 ↔ (s : G) ∈ Q) ∧
        ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
          ψ (M₀.π ((s : G) * x * (s : G)⁻¹)) = φ s (ψ (M₀.π x)) := by
  let φ : Lgen M (LB M Q B) →* (E3UWspace σ e' ≃ₗ[K] E3UWspace σ e') :=
    { toFun := fun s => transportU ψ (T s)
      map_one' := by rw [map_one]; exact transportU_one ψ
      map_mul' := fun a b => by rw [map_mul]; exact transportU_mul ψ _ _ }
  have hφ : ∀ s, φ s = transportU ψ (T s) := fun s => rfl
  refine ⟨φ, hφ, ?_, ?_, ?_⟩
  ·
    show φ.range = (e3uWact σ e').range
    ext f
    simp only [MonoidHom.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨h, hh⟩ := hAT1 s
      refine ⟨h, ?_⟩
      have hTs : T s = A h := LinearEquiv.ext hh
      rw [hφ, hTs]
      exact (transportU_of_equivariant (e3uWact σ e') A ψ hψA h).symm
    · rintro ⟨h, rfl⟩
      obtain ⟨s, hs⟩ := hAT2 h
      refine ⟨s, ?_⟩
      have hTs : T s = A h := LinearEquiv.ext hs
      rw [hφ, hTs]
      exact transportU_of_equivariant (e3uWact σ e') A ψ hψA h
  ·
    intro s
    rw [hφ, ← hTker s]
    constructor
    · intro h
      apply transportU_injective ψ
      rw [h, transportU_one]
    · intro h
      rw [h, transportU_one]
  ·
    intro s x hx
    rw [hφ, transportU_apply, hTe s x hx]

end Phi

end CFSG.RankThree.GF2n.Smith81.S81V
