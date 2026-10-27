module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD1
public import CFSG.Quasithin.Vol2.Ch3E213MG41S1

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] def conjG (σ : antiSp k) (G₀ : Subgroup (antiSp k)) : Subgroup (antiSp k) :=
  G₀.comap (MulAut.conj σ).toMonoidHom

variable {σ : antiSp k} {G₀ : Subgroup (antiSp k)}

omit [CharP k 2] in
theorem mem_conjG {g : antiSp k} : g ∈ conjG σ G₀ ↔ σ * g * σ⁻¹ ∈ G₀ :=
  Iff.rfl

theorem trv_mem_conjG {z : Fin 4 → k} {c : k} :
    trv z c ∈ conjG σ G₀ ↔ trv (natAct σ z) c ∈ G₀ := by
  rw [mem_conjG, conj_trv]

theorem mem_normC_conjG {z : Fin 4 → k} :
    z ∈ Refl.normC (conjG σ G₀) ↔ natAct σ z ∈ Refl.normC G₀ := by
  constructor
  · rintro ⟨hz, hzG⟩
    exact ⟨fun h => hz (act_injective σ (by rw [h, act_zero])), trv_mem_conjG.mp hzG⟩
  · rintro ⟨hz, hzG⟩
    exact ⟨fun h => hz (by rw [h, act_zero]), trv_mem_conjG.mpr hzG⟩

theorem onePerCentre_conjG (h : Refl.OnePerCentre G₀) : Refl.OnePerCentre (conjG σ G₀) := by
  intro d hd d' hd' hcs
  obtain ⟨v, c, hv, hc, rfl⟩ := exists_eq_trv hd.2
  obtain ⟨v', c', hv', hc', rfl⟩ := exists_eq_trv hd'.2
  rw [commSpace_trv hv hc, commSpace_trv hv' hc'] at hcs
  have hv'mem : v' ∈ Submodule.span k {v} := by
    rw [hcs]
    exact Submodule.mem_span_singleton_self v'
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hv'mem
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    exact hv' hμ.symm
  have hσv : natAct σ v ≠ 0 := fun h0 => hv (act_injective σ (by rw [h0, act_zero]))
  have hσv' : natAct σ v' ≠ 0 := fun h0 => hv' (act_injective σ (by rw [h0, act_zero]))
  have hm : trv (natAct σ v) c = trv (natAct σ v') c' := by
    refine h _ ⟨trv_mem_conjG.mp hd.1, isTransvection_trv hσv hc⟩ _
      ⟨trv_mem_conjG.mp hd'.1, isTransvection_trv hσv' hc'⟩ ?_
    rw [commSpace_trv hσv hc, commSpace_trv hσv' hc', ← hμ, act_smul,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 μ hμ0)]
  have e : ∀ (u : Fin 4 → k) (a : k), trv u a = σ⁻¹ * trv (natAct σ u) a * σ⁻¹⁻¹ :=
    fun u a => by rw [conj_trv, act_inv_act]
  rw [e v c, e v' c', hm]

omit [CharP k 2] in
theorem inv_act_two {ρ : Fin 4 → k} (hσ : natAct σ (eOne k) = ρ) (x : Fin 4 → k) :
    natAct σ⁻¹ x 2 = spBil x ρ := by
  rw [← bil_eOne (natAct σ⁻¹ x), bil_act_inv, hσ]

omit [CharP k 2] in
theorem proj_inv_act_eq_zero {ρ : Fin 4 → k} (hσ : natAct σ (eOne k) = ρ) {x : Fin 4 → k}
    (hx : spBil x ρ = 0) : proj (natAct σ⁻¹ x) = 0 ↔ ∃ a : k, x = a • ρ := by
  have h2 := inv_act_two hσ x
  rw [hx] at h2
  constructor
  · intro h0
    refine ⟨natAct σ⁻¹ x 1, ?_⟩
    have hy : natAct σ⁻¹ x = natAct σ⁻¹ x 1 • eOne k := by
      have h0' := congrFun h0
      funext i
      fin_cases i
      · simpa [proj, eOne] using h0' 0
      · simp [eOne]
      · simpa [eOne] using h2
      · simpa [proj, eOne] using h0' 3
    calc x = natAct σ (natAct σ⁻¹ x) := (act_act_inv σ x).symm
      _ = natAct σ (natAct σ⁻¹ x 1 • eOne k) := congrArg (natAct σ) hy
      _ = natAct σ⁻¹ x 1 • ρ := by rw [act_smul, hσ]
  · rintro ⟨a, rfl⟩
    rw [act_smul, ← hσ, act_inv_act]
    funext i
    fin_cases i <;> simp [proj, eOne]

omit [CharP k 2] in
theorem bil_proj_of_two {x y : Fin 4 → k} (hx : x 2 = 0) (hy : y 2 = 0) :
    spBil (proj x) (proj y) = spBil x y := by
  rw [bil_proj, bil_apply, hx, hy]
  ring

end CFSG.Quasithin.Ch3E213M.G41.Big
