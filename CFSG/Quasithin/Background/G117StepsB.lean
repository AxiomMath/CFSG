module

public import CFSG.Quasithin.Background.G117NoE9
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace G117

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_S3_in_SL2 (K : Type) [Field K] [CharP K 2] [Fintype K] (hK : Fintype.card K = 4) :
    ∃ (τ γ : Matrix.SpecialLinearGroup (Fin 2) K),
      τ * τ = 1 ∧ τ ≠ 1 ∧ γ * γ * γ = 1 ∧ γ ≠ 1 ∧ τ * γ * τ⁻¹ = γ⁻¹ := by
  classical
  have hcardu : Fintype.card Kˣ = 3 := by rw [Fintype.card_units, hK]
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, u ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card Kˣ ≤ 1 := Fintype.card_le_one_iff.2 fun a b => by rw [h a, h b]
    omega
  have hu3 : u ^ 3 = 1 := by
    have := pow_card_eq_one (x := u)
    rwa [hcardu] at this
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  have hu1 : (u : K) ≠ 1 := fun h => hu (Units.ext h)
  have hum : (u : K) * (u⁻¹ : Kˣ) = 1 := u.mul_inv
  have hu3' : (u : K) * (u : K) * (u : K) = 1 := by
    have := congrArg Units.val hu3
    simpa [pow_succ, mul_assoc] using this
  have hu3inv : (u : K)⁻¹ * (u : K)⁻¹ * (u : K)⁻¹ = 1 := by
    rw [← mul_inv, ← mul_inv, hu3', inv_one]
  have hdetτ : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two, hneg]
  have hdetγ : (!![(u : K), 0; 0, ((u⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two]
  let τ : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; 1, 0], hdetτ⟩
  let γ : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![(u : K), 0; 0, ((u⁻¹ : Kˣ) : K)], hdetγ⟩
  refine ⟨τ, γ, ?_, ?_, ?_, ?_, ?_⟩
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [τ, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [τ] at this
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [γ, Matrix.mul_apply, Fin.sum_univ_two, hu3', hu3inv]
  · intro h
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [γ] at this
    exact hu this
  · rw [mul_inv_eq_iff_eq_mul]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [γ, τ, Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_one_of_central_of_prod_S3 {A : Type*} [Group A] [Finite A] {Γ H : Subgroup A}
    (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hHΓ : H ≤ Γ) {S : Type*} [Group S] (ι : ↥H ≃* (S × S))
    {τ γ : S} (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) (hγ3 : γ * γ * γ = 1) (hγ1 : γ ≠ 1)
    (hτγ : τ * γ * τ⁻¹ = γ⁻¹) {c₀ : A} (hc₀Γ : c₀ ∈ Γ) (hc₀ : ∀ h ∈ H, h * c₀ = c₀ * h)
    (hc₀3 : c₀ ^ 3 = 1) : c₀ = 1 := by
  let e₁ : S →* ↥H := ι.symm.toMonoidHom.comp (MonoidHom.inl S S)
  let e₂ : S →* ↥H := ι.symm.toMonoidHom.comp (MonoidHom.inr S S)
  have he₁ : Function.Injective e₁ := ι.symm.injective.comp (fun a b h => (Prod.ext_iff.1 h).1)
  have he₂ : Function.Injective e₂ := ι.symm.injective.comp (fun a b h => (Prod.ext_iff.1 h).2)
  have hcomm : ∀ a b : S, e₁ a * e₂ b = e₂ b * e₁ a := by
    intro a b
    show ι.symm (a, 1) * ι.symm (1, b) = ι.symm (1, b) * ι.symm (a, 1)
    rw [← map_mul, ← map_mul]
    simp
  have key : ∀ (e : S →* ↥H) (x y : S), ((e x : ↥H) : A) * (e y : A) = ((e (x * y) : ↥H) : A) :=
    fun e x y => by rw [map_mul]; rfl
  have hone : ∀ (e : S →* ↥H), ((e 1 : ↥H) : A) = 1 := fun e => by rw [map_one]; rfl
  have hord2 : ∀ (e : S →* ↥H), ((e τ : ↥H) : A) * (e τ : A) = 1 := fun e => by
    rw [key, hτ2, hone]
  have hne : ∀ (e : S →* ↥H), Function.Injective e → ∀ s : S, s ≠ 1 → ((e s : ↥H) : A) ≠ 1 :=
    fun e he s hs h => hs (he (by rw [map_one]; exact Subtype.ext h))
  have hord3 : ∀ (e : S →* ↥H), ((e γ : ↥H) : A) ^ 3 = 1 := fun e => by
    have : ((e γ : ↥H) : A) ^ 3 = ((e γ : ↥H) : A) * (e γ : A) * (e γ : A) := by
      simp [pow_succ, mul_assoc]
    rw [this, key, key, hγ3, hone]
  have hrel : ∀ (e : S →* ↥H), ((e τ : ↥H) : A) * (e γ : A) * ((e τ : ↥H) : A)⁻¹ =
      ((e γ : ↥H) : A)⁻¹ := fun e => by
    have h := congrArg (fun x : S => ((e x : ↥H) : A)) hτγ
    simpa [map_mul, map_inv] using h
  exact eq_one_of_commute_of_two_S3 hq hHΓ (e₁ τ).2 (e₁ γ).2 (e₂ τ).2 (e₂ γ).2 (hord2 e₁)
    (hne e₁ he₁ τ hτ1) (hord3 e₁) (hne e₁ he₁ γ hγ1) (hrel e₁) (hord3 e₂) (hne e₂ he₂ γ hγ1)
    (hrel e₂) (congrArg Subtype.val (hcomm γ γ)) (congrArg Subtype.val (hcomm τ γ))
    hc₀Γ hc₀ hc₀3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

end G117

end G11

end CFSG.Quasithin
