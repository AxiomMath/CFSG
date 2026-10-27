module

public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin

section Module

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem commSub_top_stable151b {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∀ c ∈ commSub (⊤ : Subgroup W) X, g c ∈ commSub (⊤ : Subgroup W) X := by
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, -, rfl⟩ := hc
    have : g (x w * w⁻¹) = (g * x * g⁻¹) (g w) * (g w)⁻¹ := by
      rw [map_mul, map_inv]
      simp [MulAut.mul_apply]
    rw [this]
    exact Subgroup.subset_closure ⟨g * x * g⁻¹, hg x hx, g w, Subgroup.mem_top _, rfl⟩
  | one => simp
  | mul c₁ c₂ _ _ ih₁ ih₂ =>
    rw [map_mul]
    exact mul_mem ih₁ ih₂
  | inv c _ ih =>
    rw [map_inv]
    exact inv_mem ih

omit [Finite W] in
theorem commSub_top_map151b {X Y : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ Y) :
    ∀ c ∈ commSub (⊤ : Subgroup W) X, g c ∈ commSub (⊤ : Subgroup W) Y := by
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, -, rfl⟩ := hc
    have : g (x w * w⁻¹) = (g * x * g⁻¹) (g w) * (g w)⁻¹ := by
      rw [map_mul, map_inv]
      simp [MulAut.mul_apply]
    rw [this]
    exact Subgroup.subset_closure ⟨g * x * g⁻¹, hg x hx, g w, Subgroup.mem_top _, rfl⟩
  | one => simp
  | mul c₁ c₂ _ _ ih₁ ih₂ =>
    rw [map_mul]
    exact mul_mem ih₁ ih₂
  | inv c _ ih =>
    rw [map_inv]
    exact inv_mem ih

omit [Finite W] in
theorem fixV_mul_eq151b {W₁ W₂ : Subgroup W} (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥)
    {a₁ a₂ : MulAut W} (h₁ : ∀ w ∈ W₁, a₁ w ∈ W₁) (h₂ : ∀ w ∈ W₂, a₂ w ∈ W₂)
    (h₁₂ : ∀ w ∈ W₂, a₁ w = w) (h₂₁ : ∀ w ∈ W₁, a₂ w = w) :
    fixV (Subgroup.zpowers (a₁ * a₂)) = fixV (Subgroup.zpowers a₁) ⊓ fixV (Subgroup.zpowers a₂) ∧
      fixV (Subgroup.zpowers a₁) ⊔ fixV (Subgroup.zpowers a₂) = ⊤ := by
  have hdec : ∀ w : W, ∃ u ∈ W₁, ∃ v ∈ W₂, w = u * v := by
    intro w
    have : w ∈ W₁ ⊔ W₂ := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup.mp this
    exact ⟨u, hu, v, hv, huv.symm⟩
  have hsplit : ∀ u ∈ W₁, ∀ v ∈ W₂, ∀ u' ∈ W₁, ∀ v' ∈ W₂, u * v = u' * v' → u = u' ∧ v = v' := by
    intro u hu v hv u' hu' v' hv' h
    have h1 : u'⁻¹ * u = v' * v⁻¹ := by
      calc u'⁻¹ * u = u'⁻¹ * (u * v) * v⁻¹ := by group
        _ = u'⁻¹ * (u' * v') * v⁻¹ := by rw [h]
        _ = v' * v⁻¹ := by group
    have hmem : u'⁻¹ * u ∈ W₁ ⊓ W₂ :=
      ⟨W₁.mul_mem (W₁.inv_mem hu') hu, h1 ▸ W₂.mul_mem hv' (W₂.inv_mem hv)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hu2 : u = u' := by
      have := congrArg (u' * ·) hmem
      simpa using this
    refine ⟨hu2, ?_⟩
    rw [hu2] at h
    exact mul_left_cancel h
  have hfix1 : ∀ u ∈ W₁, ∀ v ∈ W₂, (a₁ (u * v) = u * v ↔ a₁ u = u) := by
    intro u hu v hv
    rw [map_mul, h₁₂ v hv]
    exact mul_left_inj v
  have hfix2 : ∀ u ∈ W₁, ∀ v ∈ W₂, (a₂ (u * v) = u * v ↔ a₂ v = v) := by
    intro u hu v hv
    rw [map_mul, h₂₁ u hu]
    exact mul_right_inj u
  have hmul : ∀ u ∈ W₁, ∀ v ∈ W₂, a₁ (a₂ (u * v)) = a₁ u * a₂ v := by
    intro u hu v hv
    rw [map_mul, h₂₁ u hu, map_mul, h₁₂ _ (h₂ v hv)]
  refine ⟨?_, ?_⟩
  · ext w
    rw [Subgroup.mem_inf, mem_fixV_zpowers_iff, mem_fixV_zpowers_iff, mem_fixV_zpowers_iff]
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec w
    rw [hfix1 u hu v hv, hfix2 u hu v hv]
    constructor
    · intro h
      have h' : a₁ (a₂ (u * v)) = u * v := h
      rw [hmul u hu v hv] at h'
      exact hsplit _ (h₁ u hu) _ (h₂ v hv) u hu v hv h' |> fun e => ⟨e.1, e.2⟩
    · rintro ⟨e1, e2⟩
      show a₁ (a₂ (u * v)) = u * v
      rw [hmul u hu v hv, e1, e2]
  · refine eq_top_iff.mpr fun w _ => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec w
    rw [mul_comm]
    exact Subgroup.mul_mem_sup (mem_fixV_zpowers_iff.mpr (h₁₂ v hv))
      (mem_fixV_zpowers_iff.mpr (h₂₁ u hu))

theorem rkIdx_fixV_mul151b {W₁ W₂ : Subgroup W} (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥)
    {a₁ a₂ : MulAut W} (h₁ : ∀ w ∈ W₁, a₁ w ∈ W₁) (h₂ : ∀ w ∈ W₂, a₂ w ∈ W₂)
    (h₁₂ : ∀ w ∈ W₂, a₁ w = w) (h₂₁ : ∀ w ∈ W₁, a₂ w = w) :
    rkIdx (fixV (Subgroup.zpowers (a₁ * a₂))) =
      rkIdx (fixV (Subgroup.zpowers a₁)) + rkIdx (fixV (Subgroup.zpowers a₂)) := by
  obtain ⟨h1, h2⟩ := fixV_mul_eq151b hsup hinf h₁ h₂ h₁₂ h₂₁
  have e := rk_sup_add_rk_inf (fixV (Subgroup.zpowers a₁)) (fixV (Subgroup.zpowers a₂))
  rw [h2, ← h1, rk_top] at e
  have e1 := rk_add_rkIdx (fixV (Subgroup.zpowers (a₁ * a₂)))
  have e2 := rk_add_rkIdx (fixV (Subgroup.zpowers a₁))
  have e3 := rk_add_rkIdx (fixV (Subgroup.zpowers a₂))
  omega

omit [Finite W] in
theorem six_module151b {A₁ A₂ : Subgroup (MulAut W)}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hinf : commSub (⊤ : Subgroup W) A₁ ⊓ commSub (⊤ : Subgroup W) A₂ = ⊥) :
    (∀ a ∈ A₁, ∀ w ∈ commSub (⊤ : Subgroup W) A₁, a w ∈ commSub (⊤ : Subgroup W) A₁) ∧
    (∀ a ∈ A₂, ∀ w ∈ commSub (⊤ : Subgroup W) A₂, a w ∈ commSub (⊤ : Subgroup W) A₂) ∧
    (∀ a ∈ A₁, ∀ w ∈ commSub (⊤ : Subgroup W) A₂, a w = w) ∧
    (∀ a ∈ A₂, ∀ w ∈ commSub (⊤ : Subgroup W) A₁, a w = w) := by
  have s11 : ∀ a ∈ A₁, ∀ w ∈ commSub (⊤ : Subgroup W) A₁, a w ∈ commSub (⊤ : Subgroup W) A₁ :=
    fun a ha w hw => commSub_top_stable151b (fun x hx => by
      have := A₁.mul_mem (A₁.mul_mem ha hx) (A₁.inv_mem ha)
      exact this) w hw
  have s22 : ∀ a ∈ A₂, ∀ w ∈ commSub (⊤ : Subgroup W) A₂, a w ∈ commSub (⊤ : Subgroup W) A₂ :=
    fun a ha w hw => commSub_top_stable151b (fun x hx => by
      have := A₂.mul_mem (A₂.mul_mem ha hx) (A₂.inv_mem ha)
      exact this) w hw
  have s21 : ∀ a ∈ A₂, ∀ w ∈ commSub (⊤ : Subgroup W) A₁, a w ∈ commSub (⊤ : Subgroup W) A₁ :=
    fun a ha w hw => commSub_top_stable151b (fun x hx => by
      have h1 : x * a = a * x := hcomm x hx a ha
      have : a * x * a⁻¹ = x := by rw [← h1]; group
      rw [this]
      exact hx) w hw
  have s12 : ∀ a ∈ A₁, ∀ w ∈ commSub (⊤ : Subgroup W) A₂, a w ∈ commSub (⊤ : Subgroup W) A₂ :=
    fun a ha w hw => commSub_top_stable151b (fun x hx => by
      have h1 : a * x = x * a := hcomm a ha x hx
      have : a * x * a⁻¹ = x := by rw [h1]; group
      rw [this]
      exact hx) w hw
  refine ⟨s11, s22, fun a ha w hw => ?_, fun a ha w hw => ?_⟩
  · have hc : a w * w⁻¹ ∈ commSub (⊤ : Subgroup W) A₁ ⊓ commSub (⊤ : Subgroup W) A₂ :=
      ⟨Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top _, rfl⟩,
        (commSub (⊤ : Subgroup W) A₂).mul_mem (s12 a ha w hw)
          ((commSub (⊤ : Subgroup W) A₂).inv_mem hw)⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hc
    exact hc
  · have hc : a w * w⁻¹ ∈ commSub (⊤ : Subgroup W) A₁ ⊓ commSub (⊤ : Subgroup W) A₂ :=
      ⟨(commSub (⊤ : Subgroup W) A₁).mul_mem (s21 a ha w hw)
          ((commSub (⊤ : Subgroup W) A₁).inv_mem hw),
        Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top _, rfl⟩⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hc
    exact hc

end Module

end CFSG.Quasithin
