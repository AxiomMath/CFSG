module

public import CFSG.Quasithin.Vol2.Ch10SecE9K
public import CFSG.Quasithin.Vol2.Ch10SecE9I

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

omit [Finite G] in
theorem psi_conj {g x : G} (hg : g ∈ fsuL0 T L) (hx : x ∈ fsuL0 T L)
    (h : g * x * g⁻¹ ∈ fsuL0 T L) :
    Ψ ⟨g * x * g⁻¹, h⟩ = Ψ ⟨g, hg⟩ * Ψ ⟨x, hx⟩ * (Ψ ⟨g, hg⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]; rfl

omit [Finite G] in
theorem psi_inv {x : G} (hx : x ∈ fsuL0 T L) (h : x⁻¹ ∈ fsuL0 T L) :
    Ψ ⟨x⁻¹, h⟩ = (Ψ ⟨x, hx⟩)⁻¹ := by
  rw [← map_inv]; rfl

omit [Finite G] in
theorem mulAut_ext_mk {X : Subgroup G} {f g : MulAut (↥X ⧸ CFSG.pCore 2 ↥X)}
    (h : ∀ (x : G) (hx : x ∈ X), f (mkO2 X x hx) = g (mkO2 X x hx)) : f = g := by
  ext q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
  exact h x hx

theorem conjQuot_cases (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) (hD2 : ParData2 K E)
    {d : L32.Γ} (hd : ∀ k ∈ K, d * k * d⁻¹ * k ∈ E) {t₁ t₂ : G} (ht₁ : t₁ ∈ fsuL0 T L)
    (ht₂ : t₂ ∈ fsuL0 T L) (hΨ₁ : Ψ ⟨t₁, ht₁⟩ = (d, 1)) (hΨ₂ : Ψ ⟨t₂, ht₂⟩ = (1, d))
    (hX₁ : (XOf T L Ψ A).map (MulAut.conj t₁).toMonoidHom = XOf T L Ψ A)
    (hX₂ : (XOf T L Ψ A).map (MulAut.conj t₂).toMonoidHom = XOf T L Ψ A) {τ : G}
    (hτ : τ ∈ T1 T L) (hXτ : (XOf T L Ψ A).map (MulAut.conj τ).toMonoidHom = XOf T L Ψ A) :
    C10P34.conjQuot _ _ τ hXτ = 1 ∨ C10P34.conjQuot _ _ τ hXτ = C10P34.conjQuot _ _ t₁ hX₁ ∨
      C10P34.conjQuot _ _ τ hXτ = C10P34.conjQuot _ _ t₂ hX₂ ∨
      ∀ q, C10P34.conjQuot _ _ τ hXτ q = q⁻¹ := by
  have hXL0 := XOf_le_fsuL0 h hD
  set X := XOf T L Ψ A with hXdef
  obtain ⟨u, v, hu, hv, hact⟩ := h.hC.T1act τ hτ
  have hmemτ : ∀ x ∈ X, τ * x * τ⁻¹ ∈ X := fun x hx => by
    have := Subgroup.mem_map_of_mem (MulAut.conj τ).toMonoidHom hx
    rw [hXτ] at this; exact this
  have hmem₁ : ∀ x ∈ X, t₁ * x * t₁⁻¹ ∈ X := fun x hx => by
    have := Subgroup.mem_map_of_mem (MulAut.conj t₁).toMonoidHom hx
    rw [hX₁] at this; exact this
  have hmem₂ : ∀ x ∈ X, t₂ * x * t₂⁻¹ ∈ X := fun x hx => by
    have := Subgroup.mem_map_of_mem (MulAut.conj t₂).toMonoidHom hx
    rw [hX₂] at this; exact this
  have cτ : ∀ x (hx : x ∈ X), Ψ ⟨τ * x * τ⁻¹, hXL0 (hmemτ x hx)⟩ =
      (u * (Ψ ⟨x, hXL0 hx⟩).1 * u⁻¹, v * (Ψ ⟨x, hXL0 hx⟩).2 * v⁻¹) := fun x hx =>
    hact ⟨x, hXL0 hx⟩ (hXL0 (hmemτ x hx))
  have c₁ : ∀ x (hx : x ∈ X), Ψ ⟨t₁ * x * t₁⁻¹, hXL0 (hmem₁ x hx)⟩ =
      (d * (Ψ ⟨x, hXL0 hx⟩).1 * d⁻¹, (Ψ ⟨x, hXL0 hx⟩).2) := fun x hx => by
    rw [psi_conj ht₁ (hXL0 hx), hΨ₁]
    ext <;> simp
  have c₂ : ∀ x (hx : x ∈ X), Ψ ⟨t₂ * x * t₂⁻¹, hXL0 (hmem₂ x hx)⟩ =
      ((Ψ ⟨x, hXL0 hx⟩).1, d * (Ψ ⟨x, hXL0 hx⟩).2 * d⁻¹) := fun x hx => by
    rw [psi_conj ht₂ (hXL0 hx), hΨ₂]
    ext <;> simp
  have hK : ∀ x (hx : x ∈ X), (Ψ ⟨x, hXL0 hx⟩).1 ∈ K ∧ (Ψ ⟨x, hXL0 hx⟩).2 ∈ K := fun x hx =>
    Subgroup.mem_prod.mp (mem_prod_of_mem_XOf h hD hx)
  have hEinv : ∀ {k a b : L32.Γ}, a * k ∈ E → b * k ∈ E → a * b⁻¹ ∈ E := fun {k a b} ha hb => by
    rw [show a * b⁻¹ = (a * k) * (b * k)⁻¹ by group]
    exact E.mul_mem ha (E.inv_mem hb)
  rcases hD2.sign u hu with su | su <;> rcases hD2.sign v hv with sv | sv
  ·
    left
    refine mulAut_ext_mk fun x hx => ?_
    rw [C10P34.conjQuot_mk hXτ hx (hmemτ x hx), MulAut.one_apply]
    refine (mkO2_eq_iff h hD (hmemτ x hx) hx).mpr ?_
    rw [cτ x hx, Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv]
    exact ⟨su _ (hK x hx).1, sv _ (hK x hx).2⟩
  ·
    right; right; left
    refine mulAut_ext_mk fun x hx => ?_
    rw [C10P34.conjQuot_mk hXτ hx (hmemτ x hx), C10P34.conjQuot_mk hX₂ hx (hmem₂ x hx)]
    refine (mkO2_eq_iff h hD (hmemτ x hx) (hmem₂ x hx)).mpr ?_
    rw [cτ x hx, c₂ x hx, Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv]
    exact ⟨su _ (hK x hx).1, hEinv (sv _ (hK x hx).2) (hd _ (hK x hx).2)⟩
  ·
    right; left
    refine mulAut_ext_mk fun x hx => ?_
    rw [C10P34.conjQuot_mk hXτ hx (hmemτ x hx), C10P34.conjQuot_mk hX₁ hx (hmem₁ x hx)]
    refine (mkO2_eq_iff h hD (hmemτ x hx) (hmem₁ x hx)).mpr ?_
    rw [cτ x hx, c₁ x hx, Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv]
    exact ⟨hEinv (su _ (hK x hx).1) (hd _ (hK x hx).1), sv _ (hK x hx).2⟩
  ·
    right; right; right
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    rw [C10P34.conjQuot_mk hXτ hx (hmemτ x hx), ← QuotientGroup.mk_inv]
    refine (mkO2_eq_iff h hD (hmemτ x hx) (X.inv_mem hx)).mpr ?_
    rw [cτ x hx, psi_inv (hXL0 hx), inv_inv, Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.snd_mul]
    exact ⟨su _ (hK x hx).1, sv _ (hK x hx).2⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
