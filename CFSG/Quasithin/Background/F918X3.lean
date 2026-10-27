module

public import CFSG.Quasithin.Background.F918X0
public import CFSG.Quasithin.Background.B4ModelsApi

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin

section Twist

variable {W : Type*} [CommGroup W] {D : FFModel} {H : Subgroup (MulAut W)} {π : D.Gam →* ↥H}

theorem exists_conj_of_twist (hD : D.IsActionModel) (hπ : D.RealizesVia H ⊤ ⊥ π)
    (T : MulAut D.Mod) (θ : MulAut D.Gam)
    (hT : ∀ γ : D.Gam, T * hD.modAct γ * T⁻¹ = hD.modAct (θ γ)) :
    ∃ g : MulAut W, ∀ γ : D.Gam,
      g * ((π γ : ↥H) : MulAut W) * g⁻¹ = ((π (θ γ) : ↥H) : MulAut W) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  let e0 : W →* D.Mod := β.comp Subgroup.topEquiv.symm.toMonoidHom
  have he0inj : Function.Injective e0 := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 := (hβk ⟨w, trivial⟩).mp hw
    simpa using h1
  have he0surj : Function.Surjective e0 := fun q => by
    obtain ⟨u, hu⟩ := hβs q
    refine ⟨(u : W), ?_⟩
    change β ⟨(u : W), trivial⟩ = q
    exact hu
  let E : W ≃* D.Mod := MulEquiv.ofBijective e0 ⟨he0inj, he0surj⟩
  have hE : ∀ (γ : D.Gam) (w : W), E (((π γ : ↥H) : MulAut W) w) = hD.modAct γ (E w) := by
    intro γ w
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
    have h1 := hβe γ ⟨w, trivial⟩ m trivial (hD.sec_inv γ m m.2) hm.symm
    have h2 : E w = QuotientGroup.mk m := hm.symm
    rw [h2, FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk]
    exact h1
  let g : MulAut W := E.trans (T.trans E.symm)
  refine ⟨g, fun γ => ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  refine MulEquiv.ext fun w => ?_
  have hT' : T (hD.modAct γ (E w)) = hD.modAct (θ γ) (T (E w)) := by
    have := congrArg (fun f : MulAut D.Mod => f (T (E w))) (hT γ)
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at this
    simpa [MulAut.inv_apply_self] using this
  show E.symm (T (E (((π γ : ↥H) : MulAut W) w))) =
    ((π (θ γ) : ↥H) : MulAut W) (E.symm (T (E w)))
  rw [hE, hT']
  apply E.injective
  rw [hE]
  simp

theorem mem_realized_of_twist (hD : D.IsActionModel) (hπ : D.RealizesVia H ⊤ ⊥ π)
    (α : MulAut ↥H) (θ : MulAut D.Gam) (hθ : ∀ γ : D.Gam, α (π γ) = π (θ γ))
    (T : MulAut D.Mod) (hT : ∀ γ : D.Gam, T * hD.modAct γ * T⁻¹ = hD.modAct (θ γ)) :
    α ∈ realized H := by
  obtain ⟨g, hg⟩ := exists_conj_of_twist hD hπ T θ hT
  rw [mem_realized]
  refine ⟨g, fun l => ?_⟩
  obtain ⟨γ, rfl⟩ := hπ.1 l
  rw [hg γ, hθ γ]

theorem exists_conj_of_twist_topBot (hD : D.IsActionModel) (hsec : D.sec = ⊤) (hker : D.ker = ⊥)
    (hπ : D.RealizesVia H ⊤ ⊥ π) (T : MulAut D.Amb) (θ : MulAut D.Gam)
    (hT : ∀ (γ : D.Gam) (x : D.Amb), T (D.act γ x) = D.act (θ γ) (T x)) :
    ∃ g : MulAut W, ∀ γ : D.Gam,
      g * ((π γ : ↥H) : MulAut W) * g⁻¹ = ((π (θ γ) : ↥H) : MulAut W) := by
  let Q : D.Mod →* D.Amb := QuotientGroup.lift (D.ker.subgroupOf D.sec) D.sec.subtype (by
    intro m hm
    rw [Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot] at hm
    exact hm)
  have hQmk : ∀ m : ↥D.sec, Q (QuotientGroup.mk m) = (m : D.Amb) := fun m => rfl
  have hQinj : Function.Injective Q := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hQmk] at hq
    have : m = 1 := Subtype.ext hq
    rw [this]
    rfl
  have hQsurj : Function.Surjective Q := fun x => by
    refine ⟨QuotientGroup.mk ⟨x, by rw [hsec]; trivial⟩, rfl⟩
  let QE : D.Mod ≃* D.Amb := MulEquiv.ofBijective Q ⟨hQinj, hQsurj⟩
  have hQact : ∀ (γ : D.Gam) (q : D.Mod), QE (hD.modAct γ q) = D.act γ (QE q) := by
    intro γ q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  refine exists_conj_of_twist hD hπ (QE.trans (T.trans QE.symm)) θ (fun γ => ?_)
  rw [mul_inv_eq_iff_eq_mul]
  refine MulEquiv.ext fun q => ?_
  apply QE.injective
  show QE (QE.symm (T (QE (hD.modAct γ q)))) = QE (hD.modAct (θ γ) (QE.symm (T (QE q))))
  rw [hQact, hQact, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hT]

theorem mem_realized_of_twist_topBot (hD : D.IsActionModel) (hsec : D.sec = ⊤) (hker : D.ker = ⊥)
    (hπ : D.RealizesVia H ⊤ ⊥ π) (α : MulAut ↥H) (θ : MulAut D.Gam)
    (hθ : ∀ γ : D.Gam, α (π γ) = π (θ γ)) (T : MulAut D.Amb)
    (hT : ∀ (γ : D.Gam) (x : D.Amb), T (D.act γ x) = D.act (θ γ) (T x)) : α ∈ realized H := by
  obtain ⟨g, hg⟩ := exists_conj_of_twist_topBot hD hsec hker hπ T θ hT
  rw [mem_realized]
  refine ⟨g, fun l => ?_⟩
  obtain ⟨γ, rfl⟩ := hπ.1 l
  rw [hg γ, hθ γ]

end Twist

end CFSG.Quasithin.F918X
