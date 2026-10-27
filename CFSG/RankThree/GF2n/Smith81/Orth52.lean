module

public import CFSG.RankThree.GF2n.Smith81.Orth52Std
public import CFSG.RankThree.GF2n.Smith81.OrthFrameChange
public import CFSG.RankThree.GF2n.Smith81.Orth25Conj
public import CFSG.RankThree.GF2n.Smith81.OrthCountAct

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped Matrix

theorem width_eq_of_width {G : Type} [Group G] {Q Z : Subgroup G} (hZ : 2 ≤ Nat.card Z)
    {n₁ n₂ : ℕ} (h₁ : Width Q Z n₁) (h₂ : Width Q Z n₂) : n₁ = n₂ := by
  unfold Width at h₁ h₂
  rw [h₁] at h₂
  have := Nat.pow_right_injective hZ h₂
  omega

private theorem inv_col_eq {K : Type} [Field K] {h : GL (Fin 2) K} {c : Fin 2 → K}
    (hh : (h : Matrix (Fin 2) (Fin 2) K) *ᵥ c = ![1, 0]) :
    ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = c 0 ∧
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = c 1 := by
  have hc : c = ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] := by
    rw [← hh, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero] at h0 h1
  exact ⟨h0.symm, h1.symm⟩

theorem smith52Act_of (h25 : Smith25OrthStatement) (hT : OrthTacitStatement) :
    Smith52ActStatement := by
  intro G _ _ M Q Z B hc K _ _ _ γ M₀ hD ι _ _ qU φ hF hAct A hA hAQ hAZ c₁ c₂ u hc12 hu0
    hqu hex
  obtain ⟨a, haA, ha1, hpa⟩ := hex
  have hcB : Ctx M Q Z B := hc.ctx
  have hcA : Ctx M Q Z A := ⟨hcB.hyp, hA, hAQ, hAZ⟩
  have hno : NoA2 Q Z (LB M Q A) := (hT G M Q Z B hc A hcA).1
  have hLA : LB M Q A ≤ Lgen M (LB M Q B) := LB_le_Lgen_of_25 h25 hc hcA
  have hn : 4 ≤ Fintype.card ι := by
    obtain ⟨n, hw, -, h4⟩ := hc.orth.exists_width
    have hZ : 2 ≤ Nat.card Z := by have := hcB.hyp.q4; omega
    rw [width_eq_of_width hZ (width_of_tensor hD φ) hw]
    exact h4
  set c : Fin 2 → K := ![c₁, c₂] with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    rcases hc12 with h1 | h1
    · exact h1 (by simpa [hcdef] using congrFun h0 0)
    · exact h1 (by simpa [hcdef] using congrFun h0 1)
  obtain ⟨h, hdet, hh⟩ := exists_SL_mulVec_eq c hc0
  obtain ⟨hi0, hi1⟩ := inv_col_eq hh
  set φ' := φ.trans (orthTensorEquiv h) with hφ'
  have hF' : OrthPreFrame Q Z M₀ qU φ' := (OrthFrame.toPreFrame hF).change hdet
  have hAct' : OrthAct Q Z M₀ qU φ' (Lgen M (LB M Q B)) := hAct.change hdet
  have hpa' : φ' (M₀.π a) = (u, 0) := by
    rw [hφ', LinearEquiv.trans_apply, hpa, orthTensorEquiv_apply]
    have e : ((c₁ • u, c₂ • u) : (ι → K) × (ι → K)) = (c 0 • u, c 1 • u) := by simp [hcdef]
    rw [e, orthTensor_pure_apply, hh]
    simp
  have key := img_inf_QB_eq_perpLine hcB hcA hno hLA hD hF' hAct' hn hu0 hqu haA ha1 hpa'
  have hback : ∀ e : M₀.E,
      φ e = orthTensor ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) id (φ' e) := by
    intro e
    rw [hφ', LinearEquiv.trans_apply]
    exact ((orthTensorEquiv h).symm_apply_apply (φ e)).symm
  refine ⟨fun v hv => ?_, fun w s t hw => ?_⟩
  ·
    have hvQ : v ∈ Q := (Subgroup.mem_inf.mp hv).1
    have hmem := (key (M₀.π v)).mp (M₀.pi_mem_img hv hvQ)
    obtain ⟨hw', ht'⟩ := mem_perpLine.mp hmem
    obtain ⟨t', ht'eq⟩ := Submodule.mem_span_singleton.mp ht'
    refine ⟨(φ' (M₀.π v)).1,
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 * t',
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 * t', hw', ?_⟩
    rw [hback, orthTensor, ← ht'eq, hi0, hi1]
    simp [hcdef, mul_smul]
  ·
    set p : (ι → K) × (ι → K) := (c₁ • w + s • u, c₂ • w + t • u) with hp
    have hp' : orthTensor (h : Matrix (Fin 2) (Fin 2) K) id p ∈ perpLine qU u := by
      rw [mem_perpLine]
      have hc0' : (h : Matrix (Fin 2) (Fin 2) K) 0 0 * c₁ +
          (h : Matrix (Fin 2) (Fin 2) K) 0 1 * c₂ = 1 := by
        have := congrFun hh 0
        simpa [hcdef, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      have hc1' : (h : Matrix (Fin 2) (Fin 2) K) 1 0 * c₁ +
          (h : Matrix (Fin 2) (Fin 2) K) 1 1 * c₂ = 0 := by
        have := congrFun hh 1
        simpa [hcdef, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      have e1 : (orthTensor (h : Matrix (Fin 2) (Fin 2) K) id p).1 =
          w + ((h : Matrix (Fin 2) (Fin 2) K) 0 0 * s +
            (h : Matrix (Fin 2) (Fin 2) K) 0 1 * t) • u := by
        simp only [orthTensor, hp, id_eq]
        linear_combination (norm := module) hc0' • w
      have e2 : (orthTensor (h : Matrix (Fin 2) (Fin 2) K) id p).2 =
          ((h : Matrix (Fin 2) (Fin 2) K) 1 0 * s +
            (h : Matrix (Fin 2) (Fin 2) K) 1 1 * t) • u := by
        simp only [orthTensor, hp, id_eq]
        linear_combination (norm := module) hc1' • w
      refine ⟨?_, ?_⟩
      · rw [e1, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_self,
          hqu, hw]
        simp
      · rw [e2]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have hpre := (key (φ'.symm (orthTensor (h : Matrix (Fin 2) (Fin 2) K) id p))).mpr
      (by rw [LinearEquiv.apply_symm_apply]; exact hp')
    obtain ⟨v, hv, hvQ, hve⟩ := hpre
    refine ⟨v, hv, ?_⟩
    rw [hve, hback, LinearEquiv.apply_symm_apply]
    exact (orthTensorEquiv h).symm_apply_apply p

end CFSG.RankThree.GF2n.Smith81
