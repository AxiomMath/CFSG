module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD7
public import CFSG.Quasithin.Vol2.Ch3E213MG41PD9

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

structure SplitA (G₀ : Subgroup (antiSp k)) (ρ x₁ x₂ : Fin 4 → k) : Prop where
  form : ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
    Q ρ = 0 ∧ ∀ x ∈ Refl.normC G₀, spBil x ρ = 0 → x ∉ k ∙ ρ → Q x = 1
  span : (∀ x ∈ Refl.normC G₀, ∀ x' ∈ Refl.normC G₀, spBil x ρ = 0 → x ∉ k ∙ ρ →
      x' - x ∈ k ∙ ρ → x' = x) →
    ∀ x ∈ Refl.normC G₀, spBil x ρ = 0 → x ∉ k ∙ ρ → ∃ α β : k, x = α • x₁ + β • x₂

structure SplitB (G₀ : Subgroup (antiSp k)) (ρ : Fin 4 → k) : Prop where
  form : ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
    Q ρ ≠ 0 ∧ ∀ x ∈ Refl.normC G₀, spBil x ρ = 0 → x ∉ k ∙ ρ → Q x = 1
  cover : ∃ F₁ : Subfield k, 4 ≤ Nat.card F₁ ∧ ∀ x ∈ Refl.normC G₀, spBil x ρ = 0 →
    x ∉ k ∙ ρ → ∀ μ ∈ F₁, μ ≠ 0 → ∃ x' ∈ Refl.normC G₀, x' - μ • x ∈ k ∙ ρ

variable {σ : antiSp k} {ρ : Fin 4 → k}

omit [CharP k 2] in
theorem exists_pullback (hσ : natAct σ (eOne k) = ρ) (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) :
    ∃ Q' : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q' x y = spBil x y) ∧
      Q' ρ = Q (eOne k) ∧ ∀ x, Q' x = Q (natAct σ⁻¹ x) := by
  refine ⟨Q.comp (natLin σ⁻¹), fun x y => ?_, ?_, fun x => ?_⟩
  · have h := hQ (natAct σ⁻¹ x) (natAct σ⁻¹ y)
    rw [bil_act] at h
    simp only [QuadraticMap.polar, QuadraticMap.comp_apply, natLin_apply', act_add] at h ⊢
    exact h
  · rw [QuadraticMap.comp_apply, natLin_apply', ← hσ, act_inv_act]
  · rw [QuadraticMap.comp_apply, natLin_apply']

theorem mem_cenT_conjG {G₀ : Subgroup (antiSp k)} (hσ : natAct σ (eOne k) = ρ) {x : Fin 4 → k}
    (hx : x ∈ Refl.normC G₀) (hxρ : spBil x ρ = 0) : natAct σ⁻¹ x ∈ cenT (conjG σ G₀) :=
  ⟨mem_normC_conjG.mpr (by rw [act_act_inv]; exact hx), by rw [inv_act_two hσ, hxρ]⟩

omit [CharP k 2] in
theorem mem_span_iff_proj (hσ : natAct σ (eOne k) = ρ) {x : Fin 4 → k} (hxρ : spBil x ρ = 0) :
    x ∈ k ∙ ρ ↔ proj (natAct σ⁻¹ x) = 0 := by
  rw [proj_inv_act_eq_zero hσ hxρ, Submodule.mem_span_singleton]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

omit [CharP k 2] in
theorem proj_sub (x y : Fin 4 → k) : proj (x - y) = proj x - proj y := by
  funext i
  fin_cases i <;> simp [proj]

theorem split_at [Finite k]
    {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) {G₀ : Subgroup (antiSp k)}
    (hone : Refl.OnePerCentre G₀)
    (hL4 : ∀ (G : Subgroup (antiSp k)) (F : Subfield k) (e e' : Fin 4 → k),
      Refl.OnePerCentre G → CaseB G F e e' →
      ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
        Q (eOne k) ≠ 0 ∧ ∀ z ∈ Refl.normC G, z 2 = 0 → proj z ≠ 0 → Q z = 1)
    (hρ : ρ ≠ 0) {x₁ x₂ : Fin 4 → k} (hx₁ : x₁ ∈ Refl.normC G₀) (hx₂ : x₂ ∈ Refl.normC G₀)
    (h₁ : spBil x₁ ρ = 0) (h₂ : spBil x₂ ρ = 0) (hc : spBil x₁ x₂ ≠ 0) :
    SplitA G₀ ρ x₁ x₂ ∨ SplitB G₀ ρ := by
  obtain ⟨σ, hσ⟩ := exists_act_eOne hρ
  have hz₁ := mem_cenT_conjG hσ hx₁ h₁
  have hz₂ := mem_cenT_conjG hσ hx₂ h₂
  have hcz : spBil (proj (natAct σ⁻¹ x₁)) (proj (natAct σ⁻¹ x₂)) ≠ 0 := by
    rw [bil_proj_of_two hz₁.2 hz₂.2, bil_act]
    exact hc
  have hcen' : ∀ z ∈ cenT (conjG σ G₀),
      natAct σ z ∈ Refl.normC G₀ ∧ spBil (natAct σ z) ρ = 0 := fun z hz =>
    ⟨mem_normC_conjG.mp hz.1, by rw [← hσ, bil_act, bil_eOne, hz.2]⟩
  have hpn : ∀ x, spBil x ρ = 0 → x ∉ k ∙ ρ → proj (natAct σ⁻¹ x) ≠ 0 := fun x hxρ hxn h =>
    hxn ((mem_span_iff_proj hσ hxρ).mpr h)
  rcases caseA_or_caseB hn hk hz₁.1 hz₂.1 hz₁.2 hz₂.2 hcz with hA | ⟨F₁, hB⟩
  · left
    refine ⟨?_, ?_⟩
    · obtain ⟨Q, hQ, hQe, -, -, hQ1⟩ := CaseA.form hA hz₁ hz₂ hcz
      obtain ⟨Q', hQ', hQ'ρ, hQ'x⟩ := exists_pullback hσ Q hQ
      refine ⟨Q', hQ', by rw [hQ'ρ, hQe], fun x hx hxρ hxn => ?_⟩
      rw [hQ'x]
      exact hQ1 _ (mem_cenT_conjG hσ hx hxρ) (hpn x hxρ hxn)
    · intro hfib x hx hxρ hxn
      have hfib' : ∀ z ∈ cenT (conjG σ G₀), ∀ z' ∈ cenT (conjG σ G₀), proj z ≠ 0 →
          proj z = proj z' → z = z' := by
        intro z hz z' hz' hpz hzz'
        obtain ⟨hz1, hz2⟩ := hcen' z hz
        obtain ⟨hz'1, hz'2⟩ := hcen' z' hz'
        have hxn' : natAct σ z ∉ k ∙ ρ := fun h =>
          hpz (by rwa [mem_span_iff_proj hσ hz2, act_inv_act] at h)
        have hdiff : natAct σ z' - natAct σ z ∈ k ∙ ρ := by
          rw [mem_span_iff_proj hσ (by rw [LinearMap.map_sub₂, hz'2, hz2, sub_zero]),
            act_sub_vec, act_inv_act, act_inv_act, proj_sub, hzz', sub_self]
        exact act_injective σ (hfib _ hz1 _ hz'1 hz2 hxn' hdiff).symm
      obtain ⟨α, β, h⟩ := CaseA.mem_span hA hz₁ hz₂ (mem_cenT_conjG hσ hx hxρ) hcz
        (hpn x hxρ hxn) hfib'
      refine ⟨α, β, act_injective σ⁻¹ ?_⟩
      rw [h, act_add, act_smul, act_smul]
  · right
    refine ⟨?_, ?_⟩
    · obtain ⟨Q, hQ, hQe, hQ1⟩ := hL4 _ F₁ _ _ (onePerCentre_conjG hone) hB
      obtain ⟨Q', hQ', hQ'ρ, hQ'x⟩ := exists_pullback hσ Q hQ
      refine ⟨Q', hQ', by rw [hQ'ρ]; exact hQe, fun x hx hxρ hxn => ?_⟩
      rw [hQ'x]
      have hz := mem_cenT_conjG hσ hx hxρ
      exact hQ1 _ hz.1 hz.2 (hpn x hxρ hxn)
    · refine ⟨F₁, hB.four, fun x hx hxρ hxn μ hμ hμ0 => ?_⟩
      have hz := mem_cenT_conjG hσ hx hxρ
      obtain ⟨a, ha, b, hb, hab⟩ := hB.image _ hz.1 hz.2 (hpn x hxρ hxn)
      have hab0 : μ * a ≠ 0 ∨ μ * b ≠ 0 := by
        by_contra hcon
        obtain ⟨h1, h2⟩ := not_or.mp hcon
        have ha0 : a = 0 := (mul_eq_zero.mp (not_not.mp h1)).resolve_left hμ0
        have hb0 : b = 0 := (mul_eq_zero.mp (not_not.mp h2)).resolve_left hμ0
        apply hpn x hxρ hxn
        rw [hab, ha0, hb0, zero_smul, zero_smul, add_zero]
      obtain ⟨z', hz', hz'2, hpz'⟩ :=
        hB.cover (μ * a) (F₁.mul_mem hμ ha) (μ * b) (F₁.mul_mem hμ hb) hab0
      obtain ⟨hx'1, hx'2⟩ := hcen' z' ⟨hz', hz'2⟩
      refine ⟨natAct σ z', hx'1, ?_⟩
      rw [mem_span_iff_proj hσ (by rw [LinearMap.map_sub₂, LinearMap.map_smul₂, hx'2, hxρ,
        smul_zero, sub_zero]), act_sub_vec, act_inv_act, act_smul, proj_sub, proj_smul, hpz', hab]
      simp only [smul_add, smul_smul, mul_assoc, sub_self]

end CFSG.Quasithin.Ch3E213M.G41.Big
