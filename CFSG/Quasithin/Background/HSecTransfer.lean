module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

namespace H

@[expose] def resHom {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    (hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) : ↥H →* MulAut ↥U where
  toFun h :=
    { toFun := fun u => ⟨(h : MulAut V) u, hU _ h.2 _ u.2⟩
      invFun := fun u => ⟨(h : MulAut V)⁻¹ u, hU _ (H.inv_mem h.2) _ u.2⟩
      left_inv := fun u => Subtype.ext ((h : MulAut V).symm_apply_apply (u : V))
      right_inv := fun u => Subtype.ext ((h : MulAut V).apply_symm_apply (u : V))
      map_mul' := fun u w => Subtype.ext (map_mul (h : MulAut V) (u : V) w) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

theorem coe_resHom_apply {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    (hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (h : ↥H) (u : ↥U) :
    ((resHom hU h u : ↥U) : V) = (h : MulAut V) u :=
  rfl

theorem FFModel.realizes_of_equiv {V W : Type*} [CommGroup V] [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut V)} {U : Subgroup V} {K : Subgroup (MulAut W)}
    (hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (j : ↥U ≃* W) (r : ↥H ≃* ↥K)
    (hr : ∀ (h : ↥H) (u : ↥U),
      ((r h : ↥K) : MulAut W) (j u) = j ⟨(h : MulAut V) u, hU _ h.2 _ u.2⟩)
    (hK : D.Realizes K ⊤ ⊥) : D.Realizes H U ⊥ := by
  obtain ⟨π, hπs, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := hK
  let jt : ↥U →* ↥(⊤ : Subgroup W) := j.toMonoidHom.codRestrict ⊤ fun _ => Subgroup.mem_top _
  refine ⟨r.symm.toMonoidHom.comp π, r.symm.surjective.comp hπs, bot_le, hks,
    fun h u hu => hU _ h.2 _ hu, fun h z hz => ?_, hsec, hker, β.comp jt, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro y
    obtain ⟨w, hw⟩ := hβs y
    refine ⟨j.symm w, ?_⟩
    have e : jt (j.symm w) = w := Subtype.ext (j.apply_symm_apply (w : W))
    change β (jt (j.symm w)) = y
    rw [e, hw]
  · intro u
    change β (jt u) = 1 ↔ _
    rw [hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    change j u = 1 ↔ (u : V) = 1
    rw [map_eq_one_iff j j.injective]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  · intro γ u m hu hm hβu
    have e1 : ((r (r.symm (π γ)) : ↥K) : MulAut W) = π γ := by rw [MulEquiv.apply_symm_apply]
    have e2 : jt ⟨((r.symm (π γ) : ↥H) : MulAut V) (u : V), hu⟩ =
        ⟨((π γ : ↥K) : MulAut W) (jt u : W), Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      change j ⟨((r.symm (π γ) : ↥H) : MulAut V) (u : V), hu⟩ = ((π γ : ↥K) : MulAut W) (j u)
      rw [← e1, hr]
    change β (jt ⟨((r.symm (π γ) : ↥H) : MulAut V) (u : V), hu⟩) = _
    rw [e2]
    exact hβe γ (jt u) m (Subgroup.mem_top _) hm hβu

end H

end CFSG.Quasithin
