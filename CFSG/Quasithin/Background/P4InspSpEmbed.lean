module

public import CFSG.Quasithin.Background.P4InspSpModel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix

namespace G11

namespace P4InspSp

theorem p4inspsp_permAct_mem (σ : Equiv.Perm (Fin 6)) {x : Fin 6 → ZMod 2} (hx : x ∈ permCore 6) :
    permAct σ x ∈ permCore 6 := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, permAct σ x i = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

theorem p4inspsp_dot_permAct (σ : Equiv.Perm (Fin 6)) (x y : Fin 6 → ZMod 2) :
    permAct σ x ⬝ᵥ permAct σ y = x ⬝ᵥ y := by
  simp only [dotProduct, permAct]
  exact Equiv.sum_comp σ⁻¹ (fun m => x m * y m)

theorem p4inspsp_perm_eq_one : ∀ σ : Equiv.Perm (Fin 6),
    (∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 →
      (permAct σ x - x = 0 ∨ ∀ i, (permAct σ x - x) i = 1)) → σ = 1 := by decide +kernel

@[expose] def permLin (σ : Equiv.Perm (Fin 6)) : ↥(permCore 6) →ₗ[ZMod 2] ↥(permCore 6) where
  toFun x := ⟨permAct σ x, p4inspsp_permAct_mem σ x.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

theorem permLin_coe (σ : Equiv.Perm (Fin 6)) (x : ↥(permCore 6)) :
    ((permLin σ x : ↥(permCore 6)) : Fin 6 → ZMod 2) = permAct σ x := rfl

theorem permLin_mul (σ τ : Equiv.Perm (Fin 6)) (x : ↥(permCore 6)) :
    permLin (σ * τ) x = permLin σ (permLin τ x) := by
  apply Subtype.ext
  funext i
  simp [permLin_coe, permAct]

theorem permLin_one (x : ↥(permCore 6)) : permLin 1 x = x := by
  apply Subtype.ext
  funext i
  simp [permLin_coe, permAct]

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

namespace A6Model

variable {f : LinearMap.BilinForm (ZMod 2) U} (M : A6Model f)

@[expose] noncomputable def sec : U →ₗ[ZMod 2] ↥(permCore 6) :=
  (LinearMap.exists_rightInverse_of_surjective M.β (LinearMap.range_eq_top.2 M.surj)).choose

theorem β_sec (u : U) : M.β (M.sec u) = u := by
  have h := (LinearMap.exists_rightInverse_of_surjective M.β
    (LinearMap.range_eq_top.2 M.surj)).choose_spec
  exact LinearMap.congr_fun h u

@[expose] noncomputable def act (σ : Equiv.Perm (Fin 6)) : U →ₗ[ZMod 2] U :=
  M.β ∘ₗ permLin σ ∘ₗ M.sec

theorem act_β (σ : Equiv.Perm (Fin 6)) (x : ↥(permCore 6)) :
    M.act σ (M.β x) = M.β (permLin σ x) := by
  have h0 : M.β (M.sec (M.β x) - x) = 0 := by rw [map_sub, M.β_sec, sub_self]
  have hfix : permLin σ (M.sec (M.β x) - x) = M.sec (M.β x) - x := by
    apply Subtype.ext
    funext i
    rcases (M.ker _).1 h0 with h | h
    · show ((M.sec (M.β x) - x : ↥(permCore 6)) : Fin 6 → ZMod 2) (σ⁻¹ i) =
        ((M.sec (M.β x) - x : ↥(permCore 6)) : Fin 6 → ZMod 2) i
      rw [h]
      rfl
    · show ((M.sec (M.β x) - x : ↥(permCore 6)) : Fin 6 → ZMod 2) (σ⁻¹ i) =
        ((M.sec (M.β x) - x : ↥(permCore 6)) : Fin 6 → ZMod 2) i
      rw [h, h]
  show M.β (permLin σ (M.sec (M.β x))) = M.β (permLin σ x)
  calc M.β (permLin σ (M.sec (M.β x)))
      = M.β (permLin σ (x + (M.sec (M.β x) - x))) := by rw [add_sub_cancel]
    _ = M.β (permLin σ x) + M.β (permLin σ (M.sec (M.β x) - x)) := by
        rw [map_add, map_add]
    _ = M.β (permLin σ x) := by rw [hfix, h0, add_zero]

theorem act_mul (σ τ : Equiv.Perm (Fin 6)) : M.act (σ * τ) = M.act σ ∘ₗ M.act τ :=
  LinearMap.ext fun u => by
    obtain ⟨x, rfl⟩ := M.surj u
    rw [LinearMap.comp_apply, act_β, act_β, act_β, permLin_mul]

theorem act_one : M.act 1 = LinearMap.id :=
  LinearMap.ext fun u => by
    obtain ⟨x, rfl⟩ := M.surj u
    rw [act_β, LinearMap.id_apply, permLin_one]

@[expose] noncomputable def rho : Equiv.Perm (Fin 6) →* GLV U where
  toFun σ := LinearEquiv.ofLinearMap (M.act σ) (M.act σ⁻¹)
    (by rw [← act_mul, mul_inv_cancel, act_one]) (by rw [← act_mul, inv_mul_cancel, act_one])
  map_one' := LinearEquiv.ext fun u => by
    show M.act 1 u = u
    rw [act_one]
    rfl
  map_mul' σ τ := LinearEquiv.ext fun u => by
    show M.act (σ * τ) u = M.act σ (M.act τ u)
    rw [act_mul]
    rfl

theorem rho_apply (σ : Equiv.Perm (Fin 6)) (u : U) : M.rho σ u = M.act σ u := rfl

theorem rho_β (σ : Equiv.Perm (Fin 6)) (x : ↥(permCore 6)) :
    M.rho σ (M.β x) = M.β (permLin σ x) := by
  rw [rho_apply, act_β]

theorem rho_mem (σ : Equiv.Perm (Fin 6)) : M.rho σ ∈ spSub f := by
  intro u v
  obtain ⟨x, rfl⟩ := M.surj u
  obtain ⟨y, rfl⟩ := M.surj v
  rw [rho_β, rho_β, M.isom, M.isom, permLin_coe, permLin_coe]
  exact p4inspsp_dot_permAct σ _ _

theorem rho_injective : Function.Injective M.rho := by
  refine (injective_iff_map_eq_one M.rho).2 fun σ hσ => p4inspsp_perm_eq_one σ fun x hx => ?_
  have h1 : M.β (permLin σ ⟨x, hx⟩) = M.β ⟨x, hx⟩ := by
    rw [← rho_β]
    have := LinearEquiv.congr_fun hσ (M.β ⟨x, hx⟩)
    simpa using this
  have h2 : M.β (permLin σ ⟨x, hx⟩ - ⟨x, hx⟩) = 0 := by rw [map_sub, h1, sub_self]
  exact (M.ker _).1 h2

end A6Model

theorem p4inspsp_exists_embedding [Finite U] {f : LinearMap.BilinForm (ZMod 2) U}
    (h : IsSymplectic f) (hd : Module.finrank (ZMod 2) U = 4) (M : A6Model f) :
    ∃ ρ : Equiv.Perm (Fin 6) →* GLV U, Function.Injective ρ ∧ (∀ σ, ρ σ ∈ spSub f) ∧
      (∀ σ x, ρ σ (M.β x) = M.β (permLin σ x)) ∧ spSub f ≤ ρ.range := by
  have : Finite (GLV U) := p4inspsp_finite_glv
  refine ⟨M.rho, M.rho_injective, M.rho_mem, M.rho_β, ?_⟩
  let r : Equiv.Perm (Fin 6) → ↥(spSub f) := fun σ => ⟨M.rho σ, M.rho_mem σ⟩
  have hr : Function.Injective r := fun a b hab => M.rho_injective (congrArg Subtype.val hab)
  have hcard : Nat.card ↥(spSub f) ≤ Nat.card (Equiv.Perm (Fin 6)) := by
    rw [p4inspsp_card_spSub_four h hd, Nat.card_perm, Nat.card_fin]
    decide
  intro g hg
  obtain ⟨σ, hσ⟩ := (hr.bijective_of_nat_card_le hcard).2 ⟨g, hg⟩
  exact ⟨σ, congrArg Subtype.val hσ⟩

end P4InspSp

end G11

end CFSG.Quasithin
