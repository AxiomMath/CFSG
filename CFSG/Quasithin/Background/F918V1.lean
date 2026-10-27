module

public import CFSG.Quasithin.Background.F918V0
public import CFSG.Quasithin.Background.F918H3
import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.B4Statement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix

theorem exists_model8 {X : Type} [CommGroup X] [Finite X] {Lb N : Subgroup (MulAut X)}
    {V₁ : Subgroup X} {A₀ : Subgroup (MulAut X)} (hLV : Lb ≤ stabSub V₁)
    (h : B42Case8 (autSub (Lb ⊔ N) V₁) (autSub Lb V₁) (autSub A₀ V₁)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) (θ : ↥Lb →* ↥Γ)
      (Θ : ↥V₁ ≃* Multiplicative (Fin 3 → K)),
      IsValentiner K Γ ∧ Function.Surjective θ ∧
      (∀ (l : ↥Lb) (v : ↥V₁),
        Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = natAct Γ (θ l) (Θ v)) ∧
      ffJ (autSub (Lb ⊔ N) V₁) = autSub Lb V₁ := by
  obtain ⟨hJ, -, -, K, _, _, Γ, hK4, hdet, hhat, hcen, π, hπ, -⟩ := h
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.nat Γ) rfl hπ
  let Θ : ↥V₁ ≃* Multiplicative (Fin 3 → K) := E.trans Subgroup.topEquiv
  have hΘ : ∀ (γ : ↥Γ) (v : ↥V₁),
      Θ (((π γ : ↥(autSub Lb V₁)) : MulAut ↥V₁) v) = natAct Γ γ (Θ v) := fun γ v => hE γ v
  have hinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful Γ)
  let e : ↥Γ ≃* ↥(autSub Lb V₁) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hmem : ∀ l : ↥Lb, resHomOn V₁ hLV l ∈ autSub Lb V₁ := fun l => by
    rw [autSub_eq_range_resHomOn hLV]
    exact ⟨l, rfl⟩
  let ρ : ↥Lb →* ↥(autSub Lb V₁) := (resHomOn V₁ hLV).codRestrict (autSub Lb V₁) hmem
  have hρ : Function.Surjective ρ := by
    rintro ⟨φ, hφ⟩
    rw [autSub_eq_range_resHomOn hLV] at hφ
    obtain ⟨l, rfl⟩ := hφ
    exact ⟨l, rfl⟩
  refine ⟨K, inferInstance, inferInstance, Γ, e.symm.toMonoidHom.comp ρ, Θ,
    ⟨hK4, hdet, hhat, hcen⟩, e.symm.surjective.comp hρ, fun l v => ?_, hJ⟩
  have hπl : π (e.symm (ρ l)) = ρ l := e.apply_symm_apply (ρ l)
  have h := hΘ (e.symm (ρ l)) v
  rw [hπl] at h
  exact h

theorem model_theta_eq_one_iff8 {X : Type} [CommGroup X] {Lb : Subgroup (MulAut X)}
    {V : Subgroup X} (hLV : Lb ≤ stabSub V) {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (θ : ↥Lb →* ↥Γ)
    (Θ : ↥V ≃* Multiplicative (Fin 3 → K))
    (hΘ : ∀ (l : ↥Lb) (v : ↥V),
      Θ ((resHomOn V hLV l : MulAut ↥V) v) = natAct Γ (θ l) (Θ v)) (l : ↥Lb) :
    θ l = 1 ↔ resHomOn V hLV l = 1 := by
  constructor
  · intro h
    ext v
    have h1 := hΘ l v
    have h0 : natAct Γ (θ l) (Θ v) = Θ v := by
      rw [h]
      simp [natAct]
    rw [h0] at h1
    exact congrArg (fun u : ↥V => (u : X)) (Θ.injective h1)
  · intro h
    apply natAct_faithful
    intro m
    obtain ⟨v, rfl⟩ := Θ.surjective m
    rw [← hΘ, h]
    simp

end CFSG.Quasithin
