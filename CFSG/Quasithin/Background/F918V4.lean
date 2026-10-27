module

public import CFSG.Quasithin.Background.F918T5
public import CFSG.Quasithin.Background.B4ModelsAction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix

section Twisted

variable {X : Type} [CommGroup X]

theorem theta2_equivariant8 {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hLV : Lb ≤ stabSub V₁) (h1 : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb) (h2 : ∀ l ∈ Lb, t * l * t⁻¹ ∈ Lb)
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (θ : ↥Lb →* ↥Γ) (Θ : ↥V₁ ≃* Multiplicative (Fin 3 → K))
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁),
      Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = natAct Γ (θ l) (Θ v))
    (x : MulAut X) (hx : x ∈ Lb) (w : ↥(V₁.map t.toMonoidHom))
    (hxw : x (w : X) ∈ V₁.map t.toMonoidHom) :
    ((restrictAutEquiv t V₁).symm.trans Θ) ⟨x (w : X), hxw⟩ =
      natAct Γ (θ ((conjAutByInv Lb t h1 h2) ⟨x, hx⟩)) (((restrictAutEquiv t V₁).symm.trans Θ) w) := by
  have : (restrictAutEquiv t V₁).symm ⟨x (w : X), hxw⟩ =
      (resHomOn V₁ hLV ((conjAutByInv Lb t h1 h2) ⟨x, hx⟩) : MulAut ↥V₁) ((restrictAutEquiv t V₁).symm w) := by
    apply Subtype.ext
    simp only [restrictAutEquiv_symm_apply_coe, coe_resHomOn_apply, conjAutByInv, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      MulAut.mul_apply, MulAut.inv_apply]
    rw [MulEquiv.apply_symm_apply]
  show Θ ((restrictAutEquiv t V₁).symm ⟨x (w : X), hxw⟩) =
    natAct Γ _ (Θ ((restrictAutEquiv t V₁).symm w))
  rw [this, hΘ]

theorem twisted_model8 {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hLV : Lb ≤ stabSub V₁) (h1 : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb) (h2 : ∀ l ∈ Lb, t * l * t⁻¹ ∈ Lb)
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (θ : ↥Lb →* ↥Γ) (Θ : ↥V₁ ≃* Multiplicative (Fin 3 → K)) (hθs : Function.Surjective θ)
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁),
      Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = natAct Γ (θ l) (Θ v)) :
    ∃ (θ₂ : ↥Lb →* ↥Γ) (Θ₂ : ↥(V₁.map t.toMonoidHom) ≃* Multiplicative (Fin 3 → K)),
      (∀ l, θ₂ l = θ ((conjAutByInv Lb t h1 h2) l)) ∧ Function.Surjective θ₂ ∧
      (∀ (x : MulAut X) (hx : x ∈ Lb) (w : ↥(V₁.map t.toMonoidHom))
        (hxw : x (w : X) ∈ V₁.map t.toMonoidHom),
        Θ₂ ⟨x (w : X), hxw⟩ = natAct Γ (θ₂ ⟨x, hx⟩) (Θ₂ w)) ∧
      (∀ v : ↥V₁, Θ₂ (restrictAutEquiv t V₁ v) = Θ v) :=
  ⟨θ.comp (conjAutByInv Lb t h1 h2).toMonoidHom, (restrictAutEquiv t V₁).symm.trans Θ, fun _ => rfl,
    hθs.comp (conjAutByInv Lb t h1 h2).surjective,
    fun x hx w hxw => theta2_equivariant8 hLV h1 h2 θ Θ hΘ x hx w hxw,
    fun v => by
      show Θ ((restrictAutEquiv t V₁).symm ((restrictAutEquiv t V₁) v)) = Θ v
      rw [MulEquiv.symm_apply_apply]⟩

end Twisted

section Central

variable {X : Type} [CommGroup X]

theorem natAct_inj8 {K : Type} [Field K] (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) {γ δ : ↥Γ}
    (h : ∀ a, natAct Γ γ a = natAct Γ δ a) : γ = δ := by
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have := h (Multiplicative.ofAdd v)
  simpa [natAct] using congrArg Multiplicative.toAdd this

theorem agree_central8 [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hZ : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) (ht : t ∈ Tb) (hLV : Lb ≤ stabSub V₁)
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (θ₂ : ↥Lb →* ↥Γ) (Θ₂ : ↥(V₁.map t.toMonoidHom) ≃* Multiplicative (Fin 3 → K))
    (hθ₂s : Function.Surjective θ₂)
    (hequiv : ∀ (x : MulAut X) (hx : x ∈ Lb) (w : ↥(V₁.map t.toMonoidHom))
        (hxw : x (w : X) ∈ V₁.map t.toMonoidHom),
        Θ₂ ⟨x (w : X), hxw⟩ = natAct Γ (θ₂ ⟨x, hx⟩) (Θ₂ w))
    {a l l'' : MulAut X} (ha : a ∈ Tb) (hl : l ∈ Lb) (hl'' : l'' ∈ Lb)
    (hagree : ∀ v ∈ V₁, a v = l v) (hagree2 : ∀ w ∈ V₁.map t.toMonoidHom, a w = l'' w) :
    (θ₂ ⟨l, hl⟩)⁻¹ * θ₂ ⟨l'', hl''⟩ ∈ Subgroup.center ↥Γ := by
  have h1 : ∀ x ∈ Lb, t⁻¹ * x * t ∈ Lb := fun x hx => by
    simpa using z35_conj_mem hZ hML (Tb.inv_mem ht) hx
  have hcomm := z35_centralizes hZ hML ha hl hagree
  have hLV₂ : ∀ x ∈ Lb, ∀ w ∈ V₁.map t.toMonoidHom, x w ∈ V₁.map t.toMonoidHom :=
    fun x hx w hw => mem_map_of_conj hLV h1 hx hw
  have hyL : l⁻¹ * l'' ∈ Lb := Lb.mul_mem (Lb.inv_mem hl) hl''
  have hy : ∀ u ∈ V₁.map t.toMonoidHom, (l⁻¹ * a) u = (l⁻¹ * l'') u := fun u hu => by
    simp only [MulAut.mul_apply]
    rw [hagree2 u hu]
  have hyc : ∀ x ∈ Lb, ∀ w ∈ V₁.map t.toMonoidHom, (l⁻¹ * l'') (x w) = x ((l⁻¹ * l'') w) := by
    intro x hx w hw
    rw [← hy _ (hLV₂ x hx w hw), ← hy w hw]
    have := congrArg (fun g : MulAut X => g w) (hcomm x hx)
    simpa [MulAut.mul_apply] using this
  have hcommS : ∀ δ B, natAct Γ (θ₂ ⟨l⁻¹ * l'', hyL⟩) (natAct Γ δ B) =
      natAct Γ δ (natAct Γ (θ₂ ⟨l⁻¹ * l'', hyL⟩) B) := by
    intro δ B
    obtain ⟨x, rfl⟩ := hθ₂s δ
    obtain ⟨w, rfl⟩ := Θ₂.surjective B
    have hxw := hLV₂ (x : MulAut X) x.2 (w : X) w.2
    have hyw := hLV₂ (l⁻¹ * l'') hyL (w : X) w.2
    have e1 := hequiv (x : MulAut X) x.2 w hxw
    have e2 := hequiv (l⁻¹ * l'') hyL w hyw
    have hxyw := hLV₂ (l⁻¹ * l'') hyL ((x : MulAut X) (w : X)) hxw
    have hyxw := hLV₂ (x : MulAut X) x.2 ((l⁻¹ * l'') (w : X)) hyw
    have e3 := hequiv (l⁻¹ * l'') hyL ⟨(x : MulAut X) (w : X), hxw⟩ hxyw
    have e4 := hequiv (x : MulAut X) x.2 ⟨(l⁻¹ * l'') (w : X), hyw⟩ hyxw
    have hxy : (⟨(l⁻¹ * l'') ((x : MulAut X) (w : X)), hxyw⟩ : ↥(V₁.map t.toMonoidHom)) =
        ⟨(x : MulAut X) ((l⁻¹ * l'') (w : X)), hyxw⟩ :=
      Subtype.ext (hyc x x.2 w w.2)
    rw [e1] at e3
    rw [e2] at e4
    exact e3.symm.trans ((congrArg Θ₂ hxy).trans e4)
  have hcen : θ₂ ⟨l⁻¹ * l'', hyL⟩ ∈ Subgroup.center ↥Γ := by
    rw [Subgroup.mem_center_iff]
    intro δ
    apply natAct_inj8
    intro B
    rw [natAct_mul_act, natAct_mul_act]
    exact (hcommS δ B).symm
  have hprod : (θ₂ ⟨l, hl⟩)⁻¹ * θ₂ ⟨l'', hl''⟩ = θ₂ ⟨l⁻¹ * l'', hyL⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [hprod]
  exact hcen

end Central

end CFSG.Quasithin
