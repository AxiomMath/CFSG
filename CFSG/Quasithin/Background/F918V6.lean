module

public import CFSG.Quasithin.Background.F918V1
public import CFSG.Quasithin.Background.F918V2
public import CFSG.Quasithin.Background.F918V3
public import CFSG.Quasithin.Background.F918V4
public import CFSG.Quasithin.Background.F918V5
public import CFSG.Quasithin.Background.F918V7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix

theorem d35InspUniq8_of_core (hcore : D35ValCore) : D35InspUniq8 := by
  classical
  intro X _ _ Mb Tb Lb V₁ A t hZ hML ht htV hA hA2 hcase hoff1 hoff2
  obtain ⟨A₀, hA₀⟩ := hcase
  have hLV : Lb ≤ stabSub V₁ := z35_le_stabSub hZ hML
  have h1 : ∀ x ∈ Lb, t⁻¹ * x * t ∈ Lb := fun x hx => by
    simpa using z35_conj_mem hZ hML (Tb.inv_mem ht) hx
  have h2 : ∀ x ∈ Lb, t * x * t⁻¹ ∈ Lb := fun x hx => z35_conj_mem hZ hML ht hx
  have hTL : ∀ s ∈ Tb, ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb := fun s hs l hl => z35_conj_mem hZ hML hs hl
  have hLV₂ : Lb ≤ stabSub (V₁.map t.toMonoidHom) := le_stabSub_map_of_conj hLV h1
  obtain ⟨K, hK, hKf, Γ, θ, Θ, hval, hθs, hΘ, hffJ⟩ := exists_model8 hLV hA₀
  obtain ⟨θ₂, Θ₂, hθ₂, hθ₂s, hequiv, hΘ₂t⟩ := twisted_model8 hLV h1 h2 θ Θ hθs hΘ
  have hffJ₂ := ffJ_map_conj hTL ht hffJ
  have hΘ₂ : ∀ (l : ↥Lb) (w : ↥(V₁.map t.toMonoidHom)),
      Θ₂ ((resHomOn (V₁.map t.toMonoidHom) hLV₂ l : MulAut ↥(V₁.map t.toMonoidHom)) w) =
        natAct Γ (θ₂ l) (Θ₂ w) := fun l w => hequiv l l.2 w _
  have hAV₂ : A ≤ Tb ⊓ stabSub (V₁.map t.toMonoidHom) := fun a ha => ⟨(hA ha).1, hA2 ha⟩
  obtain ⟨hag₁, hoffE⟩ := offender_model hLV inf_le_right hA θ Θ hθs hΘ hffJ hoff1
  obtain ⟨hag₂, hoffF⟩ := offender_model hLV₂ inf_le_right hAV₂ θ₂ Θ₂ hθ₂s hΘ₂ hffJ₂ hoff2
  have hker₁ : ∀ l : ↥Lb, θ l = 1 → l ∈ Subgroup.center ↥Lb := by
    intro l hl
    have hres := (model_theta_eq_one_iff8 hLV θ Θ hΘ l).1 hl
    have hcen := z35_central_of_trivial hZ hML l.2 (fun v hv => by
      have := congrArg (fun φ : MulAut ↥V₁ => ((φ ⟨v, hv⟩ : ↥V₁) : X)) hres
      simpa using this)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcen g g.2).symm
  have hker₂ : ∀ l : ↥Lb, θ₂ l = 1 → l ∈ Subgroup.center ↥Lb := by
    intro l hl
    rw [hθ₂] at hl
    have hc := hker₁ _ hl
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply (conjAutByInv Lb t h1 h2).injective
    rw [map_mul, map_mul]
    exact hc _
  have hk₁ := ker_quot_eq_center hZ.quasi θ hθs hker₁
  have hk₂ := ker_quot_eq_center hZ.quasi θ₂ hθ₂s hker₂
  obtain ⟨α, hα⟩ := exists_alpha θ θ₂ hθs hθ₂s (hk₁.trans hk₂.symm)
  have hrel : ((((agreeSub Lb A V₁ hLV).map θ).map (QuotientGroup.mk' (Subgroup.center ↥Γ))).map
      α.toMonoidHom) =
      ((agreeSub Lb A (V₁.map t.toMonoidHom) hLV₂).map θ₂).map
        (QuotientGroup.mk' (Subgroup.center ↥Γ)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨l, ⟨a, ha, hal⟩, rfl⟩, rfl⟩, rfl⟩
      obtain ⟨l'', hl'', hal''⟩ := hag₂ a ha
      refine ⟨θ₂ ⟨l'', hl''⟩, ⟨⟨l'', hl''⟩, ⟨a, ha, hal''⟩, rfl⟩, ?_⟩
      show QuotientGroup.mk' (Subgroup.center ↥Γ) (θ₂ ⟨l'', hl''⟩) =
        α (QuotientGroup.mk' (Subgroup.center ↥Γ) (θ l))
      rw [hα]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have hc := agree_central8 hZ hML ht hLV θ₂ Θ₂ hθ₂s hequiv (hA ha).1 l.2 hl'' hal hal''
      simpa using Subgroup.inv_mem _ hc
    · rintro ⟨_, ⟨l'', ⟨a, ha, hal''⟩, rfl⟩, rfl⟩
      obtain ⟨l, hl, hal⟩ := hag₁ a ha
      refine ⟨QuotientGroup.mk' (Subgroup.center ↥Γ) (θ ⟨l, hl⟩),
        ⟨θ ⟨l, hl⟩, ⟨⟨l, hl⟩, ⟨a, ha, hal⟩, rfl⟩, rfl⟩, ?_⟩
      show α (QuotientGroup.mk' (Subgroup.center ↥Γ) (θ ⟨l, hl⟩)) =
        QuotientGroup.mk' (Subgroup.center ↥Γ) (θ₂ l'')
      rw [hα]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact agree_central8 hZ hML ht hLV θ₂ Θ₂ hθ₂s hequiv (hA ha).1 hl l''.2 hal hal''
  obtain ⟨β, Φ, hβ, hΦ⟩ := hcore K Γ hval α _ _ hoffE hoffF hrel
  have hθβ : θ₂ = β.toMonoidHom.comp θ := by
    apply (eq_of_central_ratio hZ.quasi.1 θ₂ (β.toMonoidHom.comp θ) _)
    intro l
    have h3 : QuotientGroup.mk' (Subgroup.center ↥Γ) (θ₂ l) =
        QuotientGroup.mk' (Subgroup.center ↥Γ) (β (θ l)) := by
      rw [hβ, hα]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h3
    have hw : (β (θ l))⁻¹ * θ₂ l ∈ Subgroup.center ↥Γ := by simpa using Subgroup.inv_mem _ h3
    have h5 := Subgroup.mem_center_iff.mp hw (θ₂ l)
    have h6 : θ₂ l * (β (θ l))⁻¹ = (β (θ l))⁻¹ * θ₂ l := by
      calc θ₂ l * (β (θ l))⁻¹ = (θ₂ l * ((β (θ l))⁻¹ * θ₂ l)) * (θ₂ l)⁻¹ := by group
        _ = (((β (θ l))⁻¹ * θ₂ l) * θ₂ l) * (θ₂ l)⁻¹ := by rw [h5]
        _ = (β (θ l))⁻¹ * θ₂ l := by group
    show θ₂ l * (β (θ l))⁻¹ ∈ Subgroup.center ↥Γ
    rw [h6]
    exact hw
  have hΦ' : ∀ (l : ↥Lb) (w : Fin 3 → K),
      Φ ((((θ l : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
        ((((θ₂ l : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Φ w) := by
    intro l w
    rw [hθβ]
    exact hΦ (θ l) w
  exact false_of_intertwiner hZ hML ht htV hLV θ Θ hΘ θ₂ Θ₂ hequiv hΘ₂t Φ hΦ'

end CFSG.Quasithin
