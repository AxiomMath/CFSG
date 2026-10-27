module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CF
public import CFSG.Quasithin.Vol2.Ch3E213MP6BA
public import CFSG.Quasithin.Vol2.Ch3E213MP6CD

public section

namespace CFSG.Quasithin.Ch3E213M.P6B

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt uElt_mul antiSp_ext
  uMat_zero)

variable {k : Type} [Field k]

theorem natAct_inv_natAct (g : antiSp k) (x : Fin 4 → k) : natAct g⁻¹ (natAct g x) = x := by
  rw [← natAct_mul, inv_mul_cancel, natAct_one]

theorem natAct_natAct_inv (g : antiSp k) (x : Fin 4 → k) : natAct g (natAct g⁻¹ x) = x := by
  rw [← natAct_mul, mul_inv_cancel, natAct_one]

theorem spBil_natAct_conj (g w : antiSp k) (x : Fin 4 → k) :
    spBil x (natAct (g * w * g⁻¹) x) = spBil (natAct g⁻¹ x) (natAct w (natAct g⁻¹ x)) := by
  conv_lhs => rw [← natAct_natAct_inv g x]
  rw [natAct_mul, natAct_mul, natAct_inv_natAct, spBil_natAct]

variable [CharP k 2]

theorem uElt_center_mul_self (b c : k) : (uElt 0 b c 0 : antiSp k) * uElt 0 b c 0 = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [uElt_mul]
  refine antiSp_ext ?_
  rw [CFSG.ComponentClassification.UnbalancedCatalog.SpChain.glMat_uElt]
  change _ = (1 : Matrix (Fin 4) (Fin 4) k)
  rw [← uMat_zero]
  congr 1
  · ring
  · linear_combination b * h2
  · linear_combination c * h2
  · ring

theorem spBil_natAct_uElt_center (b c : k) (x : Fin 4 → k) :
    spBil x (natAct (uElt 0 b c 0 : antiSp k) x) = c * x 3 ^ 2 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [natAct_uElt_center, spBil_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (x 0 * x 3 + x 1 * x 2 + b * x 2 * x 3) * h2

theorem exists_spBil_uElt_center_ne_zero {b c : k} (hc : c ≠ 0) :
    ∃ x, spBil x (natAct (uElt 0 b c 0 : antiSp k) x) ≠ 0 :=
  ⟨Pi.single 3 1, by rw [spBil_natAct_uElt_center]; simpa using hc⟩

theorem spBil_eq_zero_of_swap {g : antiSp k} (hg : g * g = 1)
    {V₁ V₂ : Submodule k (Fin 4 → k)} (hV₂ : ∀ v, v ∈ V₂ ↔ ∀ w ∈ V₁, spBil w v = 0)
    (htop : V₁ ⊔ V₂ = ⊤) (h12 : ∀ v ∈ V₁, natAct g v ∈ V₂) (h21 : ∀ v ∈ V₂, natAct g v ∈ V₁)
    (x : Fin 4 → k) : spBil x (natAct g x) = 0 := by
  have hx : x ∈ V₁ ⊔ V₂ := htop ▸ Submodule.mem_top
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
  have hgg : natAct g (natAct g x₁) = x₁ := by rw [← natAct_mul, hg, natAct_one]
  have e1 : spBil x₁ (natAct g x₁) = 0 := (hV₂ _).mp (h12 x₁ hx₁) x₁ hx₁
  have e2 : spBil x₂ (natAct g x₂) = 0 := by
    rw [spBil_comm]
    exact (hV₂ _).mp hx₂ _ (h21 x₂ hx₂)
  have e3 : spBil x₂ (natAct g x₁) = spBil x₁ (natAct g x₂) := by
    rw [← spBil_natAct g x₂ (natAct g x₁), hgg, spBil_comm]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have e : spBil (x₁ + x₂) (natAct g (x₁ + x₂)) = spBil x₁ (natAct g x₁) +
      spBil x₁ (natAct g x₂) + spBil x₂ (natAct g x₁) + spBil x₂ (natAct g x₂) := by
    rw [natAct_add]
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [e, e1, e2, e3]
  linear_combination spBil x₁ (natAct g x₂) * h2

omit [CharP k 2] in
theorem natLin_mul (g h : antiSp k) : natLin (g * h) = (natLin g).comp (natLin h) := by
  ext v i
  simp [natLin_apply, natAct_mul]

omit [CharP k 2] in
theorem natLin_one : natLin (1 : antiSp k) = LinearMap.id := by
  ext v i
  simp [natLin_apply, natAct_one]

omit [CharP k 2] in
@[expose] def stabSub (X : Submodule k (Fin 4 → k)) : Subgroup (antiSp k) where
  carrier := {g | X.map (natLin g) = X}
  mul_mem' := by
    intro g h hg hh
    change X.map (natLin (g * h)) = X
    rw [natLin_mul, Submodule.map_comp]
    rw [show X.map (natLin h) = X from hh, show X.map (natLin g) = X from hg]
  one_mem' := by
    change X.map (natLin 1) = X
    rw [natLin_one, Submodule.map_id]
  inv_mem' := by
    intro g hg
    change X.map (natLin g⁻¹) = X
    have hg' : X.map (natLin g) = X := hg
    conv_lhs => rw [← hg']
    rw [← Submodule.map_comp, ← natLin_mul, inv_mul_cancel, natLin_one, Submodule.map_id]

theorem not_g41Dec_of_nonAlt {W W' : Subgroup (antiSp k)}
    (hirr : IsIrreducibleSp4 (W ⊔ W'))
    (hW : ∀ w ∈ W, w ≠ 1 → w * w = 1 ∧ ∃ x, spBil x (natAct w x) ≠ 0)
    (hW' : ∀ w ∈ W', w ≠ 1 → w * w = 1 ∧ ∃ x, spBil x (natAct w x) ≠ 0) :
    ¬ G41DecW (W ⊔ W') := by
  rintro ⟨V₁, V₂, hdim, hV₂, hdisj, hpres⟩
  have hmem₂ : ∀ v, v ∈ V₂ ↔ ∀ w ∈ V₁, spBil w v = 0 := fun v => by
    rw [hV₂]
    rfl
  have hfin := LinearMap.BilinForm.finrank_add_finrank_orthogonal spBil_isRefl V₁
  rw [← hV₂, hdim, Module.finrank_fin_fun] at hfin
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  rw [hdisj, finrank_bot, add_zero, hdim] at hsup
  have htop : V₁ ⊔ V₂ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    have h1 := Submodule.finrank_le (V₁ ⊔ V₂)
    rw [Module.finrank_fin_fun] at h1
    omega
  have hfix : ∀ g, (g = 1 ∨ (g * g = 1 ∧ ∃ x, spBil x (natAct g x) ≠ 0)) → g ∈ W ⊔ W' →
      g ∈ stabSub V₁ := by
    intro g hg hgI
    rcases hpres g hgI with h | h
    · exact h.1
    · exfalso
      rcases hg with rfl | ⟨hgg, x, hx⟩
      · rw [natLin_one, Submodule.map_id] at h
        rw [h.1, inf_idem] at hdisj
        rw [h.1, hdisj, finrank_bot] at hdim
        exact absurd hdim (by norm_num)
      · refine hx (spBil_eq_zero_of_swap hgg hmem₂ htop (fun v hv => ?_) (fun v hv => ?_) x)
        · rw [← h.1, ← natLin_apply]
          exact Submodule.mem_map_of_mem hv
        · rw [← h.2, ← natLin_apply]
          exact Submodule.mem_map_of_mem hv
  have hle : W ⊔ W' ≤ stabSub V₁ := by
    refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · by_cases h1 : w = 1
      · exact hfix w (Or.inl h1) (Subgroup.mem_sup_left hw)
      · exact hfix w (Or.inr (hW w hw h1)) (Subgroup.mem_sup_left hw)
    · by_cases h1 : w = 1
      · exact hfix w (Or.inl h1) (Subgroup.mem_sup_right hw)
      · exact hfix w (Or.inr (hW' w hw h1)) (Subgroup.mem_sup_right hw)
  rcases hirr V₁ (fun g hg v hv => by
      have h := hle hg
      change V₁.map (natLin g) = V₁ at h
      rw [← h, ← natLin_apply]
      exact Submodule.mem_map_of_mem hv) with h | h
  · rw [h, finrank_bot] at hdim
    exact absurd hdim (by norm_num)
  · rw [h, finrank_top, Module.finrank_fin_fun] at hdim
    exact absurd hdim (by norm_num)

end CFSG.Quasithin.Ch3E213M.P6B
