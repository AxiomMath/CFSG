module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredCore

public section

namespace CFSG.StandardType.LinIrred

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd CFSG.StandardType.LinUnitL

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {L' : Type} [Group L']
  {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem heart_end_pow (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    (hφ's : Function.Surjective φ') (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) (f : MulAut L' → MulAut L')
    (hfH : ∀ a ∈ Subgroup.closure (heartSet φ' p), f a ∈ Subgroup.closure (heartSet φ' p))
    (hfmul : ∀ a ∈ Subgroup.closure (heartSet φ' p), ∀ b ∈ Subgroup.closure (heartSet φ' p),
      f (a * b) = f a * f b)
    (hfW : ∀ n ∈ Set.range (fun σ : Equiv.Perm (Fin d) => φ' (permSL σ)),
      ∀ a ∈ Subgroup.closure (heartSet φ' p),
        f (MulAut.conj n * a * (MulAut.conj n)⁻¹) = MulAut.conj n * f a * (MulAut.conj n)⁻¹) :
    ∃ c : ℕ, ∀ a ∈ Subgroup.closure (heartSet φ' p), f a = a ^ c := by
  classical
  have := Fact.mk hp
  set H : Subgroup (MulAut L') := Subgroup.closure (heartSet φ' p) with hH
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  have hVA : heartSet φ' p ⊆ A := by
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have hHA : H ≤ A := (Subgroup.closure_le A).mpr hVA
  have hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := fun a ha b hb =>
    TableB.IsElemAbelian.comm hA (hHA ha) (hHA hb)
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hf1 : f 1 = 1 := by
    have h := hfmul 1 H.one_mem 1 H.one_mem
    rw [mul_one] at h
    have h2 := congrArg (fun z => (f 1)⁻¹ * z) h
    simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
    exact h2.symm
  have hfinv : ∀ a ∈ H, f a⁻¹ = (f a)⁻¹ := by
    intro a ha
    have h := hfmul a⁻¹ (H.inv_mem ha) a ha
    rw [inv_mul_cancel, hf1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hfpow : ∀ a ∈ H, ∀ m : ℕ, f (a ^ m) = (f a) ^ m := by
    intro a ha m
    induction m with
    | zero => simp [hf1]
    | succ m ih => rw [pow_succ, hfmul _ (H.pow_mem ha m) a ha, ih, pow_succ]
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set j₀ : Fin d := ⟨1, by omega⟩ with hj₀
  set k₂ : Fin d := ⟨2, by omega⟩ with hk₂
  have h01 : i₀ ≠ j₀ := by simp [hi₀, hj₀, Fin.ext_iff]
  have hk0 : k₂ ≠ i₀ := by simp [hi₀, hk₂, Fin.ext_iff]
  have hk1 : k₂ ≠ j₀ := by simp [hj₀, hk₂, Fin.ext_iff]
  have hζp : ∀ m, ggPairVec i₀ j₀ ζ m ^ p = 1 := fun m => pow_ggPairVec hζ.pow_eq_one m
  set D₁ : SpecialLinearGroup (Fin d) K :=
    diagSLOf (ggPairVec i₀ j₀ ζ) (prod_ggPairVec ζ hζ0) with hD₁
  have hD₁m : (D₁ : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec i₀ j₀ ζ) := rfl
  set a₁ : MulAut L' := MulAut.conj (φ' D₁) with ha₁def
  have ha₁H : a₁ ∈ H := Subgroup.subset_closure ⟨D₁, _, hD₁m, hζp, rfl⟩
  have ha₁act : ActsDiag φ' a₁ (ggPairVec i₀ j₀ ζ) := actsDiag_conj hD₁m
  have hconjAct : ∀ E : SpecialLinearGroup (Fin d) K, GGActsBy φ' (MulAut.conj (φ' E)) E :=
    fun E s => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  obtain ⟨w, hw⟩ := hdiag (f a₁) (hHA (hfH a₁ ha₁H))
  have hbp : (f a₁) ^ p = 1 := hAp _ (hHA (hfH a₁ ha₁H))
  have hstab : ∀ σ : Equiv.Perm (Fin d), σ i₀ = i₀ → σ j₀ = j₀ →
      MulAut.conj (φ' (permSL σ)) * a₁ * (MulAut.conj (φ' (permSL σ)))⁻¹ = a₁ := by
    intro σ hσ0 hσ1
    have h1 := ha₁act.conj_perm σ
    have e : ggPairVec i₀ j₀ ζ ∘ ⇑σ = ggPairVec i₀ j₀ ζ := by
      rw [ggPairVec_comp, (Equiv.symm_apply_eq σ).mpr hσ0.symm,
        (Equiv.symm_apply_eq σ).mpr hσ1.symm]
    rw [e] at h1
    exact h1.unique hφ's ha₁act
  have hbstab : ∀ σ : Equiv.Perm (Fin d), σ i₀ = i₀ → σ j₀ = j₀ → ∀ k, k ≠ i₀ →
      w (σ k) = w k := by
    intro σ hσ0 hσ1 k hk
    have h1 : MulAut.conj (φ' (permSL σ)) * f a₁ * (MulAut.conj (φ' (permSL σ)))⁻¹ = f a₁ := by
      rw [← hfW _ ⟨σ, rfl⟩ a₁ ha₁H, hstab σ hσ0 hσ1]
    have h2 := hw.conj_perm σ
    rw [h1] at h2
    have h3 := hw.ratio hφker h2 hk
    simp only [Function.comp_apply, hσ0] at h3
    exact (mul_right_cancel₀ (inv_ne_zero (hw.ne_zero i₀)) h3).symm
  have hw_out : ∀ k, k ≠ i₀ → k ≠ j₀ → w k = w k₂ := by
    intro k hki hkj
    by_cases hkk : k = k₂
    · rw [hkk]
    · have h := hbstab (Equiv.swap k k₂) (Equiv.swap_apply_of_ne_of_ne hki.symm hk0.symm)
        (Equiv.swap_apply_of_ne_of_ne hkj.symm hk1.symm) k hki
      rw [Equiv.swap_apply_left] at h
      exact h.symm
  set τ : Equiv.Perm (Fin d) := Equiv.swap i₀ j₀ with hτ
  have hτa₁ : MulAut.conj (φ' (permSL τ)) * a₁ * (MulAut.conj (φ' (permSL τ)))⁻¹ = a₁⁻¹ := by
    have h1 := ha₁act.conj_perm τ
    have e : ggPairVec i₀ j₀ ζ ∘ ⇑τ = fun m => (ggPairVec i₀ j₀ ζ m)⁻¹ := by
      rw [ggPairVec_comp, hτ, Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right,
        ggPairVec_swap]
    rw [e] at h1
    exact h1.unique hφ's ha₁act.inv
  have hbτ : MulAut.conj (φ' (permSL τ)) * f a₁ * (MulAut.conj (φ' (permSL τ)))⁻¹ =
      (f a₁)⁻¹ := by
    rw [← hfW _ ⟨τ, rfl⟩ a₁ ha₁H, hτa₁, hfinv a₁ ha₁H]
  have hw_sq : w k₂ * w k₂ = w i₀ * w j₀ := by
    have h2 := hw.conj_perm τ
    rw [hbτ] at h2
    have h3 := h2.ratio hφker hw.inv hk0
    simp only [Function.comp_apply, hτ, Equiv.swap_apply_of_ne_of_ne hk0 hk1,
      Equiv.swap_apply_left, inv_inv] at h3
    have e1 := hw.ne_zero k₂
    have e2 := hw.ne_zero j₀
    field_simp at h3
    linear_combination h3
  obtain ⟨c, -, hc⟩ := hζ.eq_pow_of_pow_eq_one (hw.ratio_pow hφker hbp i₀ k₂)
  have hbeq : f a₁ = a₁ ^ c := by
    have h1 : ActsDiag φ' (a₁ ^ c) (fun k => ggPairVec i₀ j₀ ζ k ^ c) := ha₁act.pow c
    have h2 := LinUnitL.ActsDiag.mul_const h1 (hw.ne_zero k₂)
    have e : (fun k => ggPairVec i₀ j₀ ζ k ^ c * w k₂) = w := by
      funext k
      by_cases hki : k = i₀
      · rw [hki, ggPairVec_apply]
        simp only [if_true, h01, if_false, mul_one]
        rw [hc]
        field_simp [hw.ne_zero k₂]
      · by_cases hkj : k = j₀
        · rw [hkj, ggPairVec_apply]
          simp only [if_true, h01.symm, if_false, one_mul, inv_pow]
          rw [hc]
          have e1 := hw.ne_zero k₂
          have e2 := hw.ne_zero i₀
          field_simp
          linear_combination hw_sq
        · rw [ggPairVec_apply]
          simp only [hki, hkj, if_false, mul_one, one_pow, one_mul]
          exact (hw_out k hki hkj).symm
    rw [e] at h2
    exact hw.unique hφ's h2
  have hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ e ∈ H, ∀ E : SpecialLinearGroup (Fin d) K,
      (E : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l (ζ ^ m)) → GGActsBy φ' e E →
      f e = e ^ c := by
    intro k l hkl m e _ E hE heE
    obtain ⟨σ, hσk, hσl⟩ := exists_perm_pair hkl h01
    have hpowmat : ((D₁ ^ m : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (ggPairVec i₀ j₀ (ζ ^ m)) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, hD₁m, diagonal_pow, ← ggPairVec_pow]
      rfl
    have hact := ((hconjAct D₁).pow m).conj (permSL σ)
    have hmat := coe_permSL_conj hpowmat σ
    rw [ggPairVec_comp_of hσk hσl] at hmat
    have hDE : E = permSL σ * D₁ ^ m * (permSL σ)⁻¹ := Subtype.ext (hE.trans hmat.symm)
    have heq : e = MulAut.conj (φ' (permSL σ)) * (a₁ ^ m) * (MulAut.conj (φ' (permSL σ)))⁻¹ := by
      subst hDE
      exact GGActsBy.unique hφ's heE hact
    rw [heq, hfW _ ⟨σ, rfl⟩ _ (H.pow_mem ha₁H m), hfpow a₁ ha₁H m, hbeq,
      show (a₁ ^ c) ^ m = (a₁ ^ m) ^ c by rw [← pow_mul, ← pow_mul, mul_comm]]
    exact conj_pow.symm
  have hP1 : f 1 = 1 ^ c := by rw [hf1, one_pow]
  have hPmul : ∀ a ∈ H, ∀ b ∈ H, f a = a ^ c → f b = b ^ c → f (a * b) = (a * b) ^ c := by
    intro a ha b hb hfa hfb
    rw [hfmul a ha b hb, hfa, hfb, Commute.mul_pow (hHcomm a ha b hb)]
  have hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ a ∈ H, ∃ D : SpecialLinearGroup (Fin d) K,
        (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧ GGActsBy φ' a D := fun t ht htp =>
    ⟨_, Subgroup.subset_closure ⟨diagSLOf t htp, t, coe_diagSLOf t htp, ht, rfl⟩,
      diagSLOf t htp, coe_diagSLOf t htp, hconjAct _⟩
  refine ⟨c, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨D, u, hD, hu, rfl⟩ := hx
    have hDp : ∏ i, u i = 1 := by
      have h := D.2
      rwa [hD, det_diagonal] at h
    obtain ⟨a', -, ha'P, E', hE', ha'E'⟩ := exists_ggActsBy_of_gen (A := H) hfull hζ hp
      (by omega) (fun e => f e = e ^ c) hP1 hPmul hPv hu hDp
    have hDE : D = E' := Subtype.ext (hD.trans hE'.symm)
    rw [GGActsBy.unique hφ's (hconjAct D) (hDE ▸ ha'E')]
    exact ha'P
  | one => rw [hf1, one_pow]
  | mul x y hxm hym hx hy =>
    rw [hfmul x hxm y hym, hx, hy, Commute.mul_pow (hHcomm x hxm y hym)]
  | inv x hxm hx => rw [hfinv x hxm, hx, inv_pow]

end CFSG.StandardType.LinIrred

end
