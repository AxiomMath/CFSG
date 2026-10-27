module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdMod
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdNbr

public section

namespace CFSG.StandardType.UnitAct

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB TypeA

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem heart_end_pow [Finite K] (hM : UnitTB.Model φ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (f : MulAut L' → MulAut L')
    (hfH : ∀ a ∈ Subgroup.closure (heartSetU φ p), f a ∈ Subgroup.closure (heartSetU φ p))
    (hfmul : ∀ a ∈ Subgroup.closure (heartSetU φ p), ∀ b ∈ Subgroup.closure (heartSetU φ p),
      f (a * b) = f a * f b)
    (hfW : ∀ x ∈ {x : L' | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hM.field σ)},
      ∀ a ∈ Subgroup.closure (heartSetU φ p),
        f (MulAut.conj x * a * (MulAut.conj x)⁻¹) = MulAut.conj x * f a * (MulAut.conj x)⁻¹) :
    ∃ c : ℕ, ∀ a ∈ Subgroup.closure (heartSetU φ p), f a = a ^ c := by
  classical
  have := Fact.mk hp
  have hd3 : 3 ≤ d := by omega
  set H : Subgroup (MulAut L') := Subgroup.closure (heartSetU φ p) with hH
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  have hVA : heartSetU φ p ⊆ A := by
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have hHA : H ≤ A := (Subgroup.closure_le A).mpr hVA
  have hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := fun a ha b hb =>
    IsElemAbelian.comm hA (hHA ha) (hHA hb)
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
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
  obtain ⟨D₁, hD₁m⟩ := exists_diagSU hM.field hpq hζp (prod_ggPairVec ζ hζ0)
  set a₁ : MulAut L' := MulAut.conj (φ D₁) with ha₁def
  have ha₁H : a₁ ∈ H := Subgroup.subset_closure ⟨D₁, _, hD₁m, hζp, rfl⟩
  have ha₁act : ActsDiagU φ a₁ (ggPairVec i₀ j₀ ζ) := actsDiagU_conj hD₁m
  obtain ⟨w, hw⟩ := hdiag (f a₁) (hHA (hfH a₁ ha₁H))
  have hbp : (f a₁) ^ p = 1 := hAp _ (hHA (hfH a₁ ha₁H))
  have hstab : ∀ σ : Equiv.Perm (Fin d), σ i₀ = i₀ → σ j₀ = j₀ →
      MulAut.conj (φ (permSU hM.field σ)) * a₁ * (MulAut.conj (φ (permSU hM.field σ)))⁻¹ = a₁ := by
    intro σ hσ0 hσ1
    have h1 := ha₁act.conj_perm hM.field σ
    have e : (fun k => ggPairVec i₀ j₀ ζ (σ⁻¹ k)) = ggPairVec i₀ j₀ ζ :=
      ggPairVec_comp_of (σ := σ⁻¹) (Equiv.Perm.inv_eq_iff_eq.mpr hσ0.symm)
        (Equiv.Perm.inv_eq_iff_eq.mpr hσ1.symm) ζ
    rw [e] at h1
    exact actsDiagU_unique hM.surj h1 ha₁act
  have hbstab : ∀ σ : Equiv.Perm (Fin d), σ i₀ = i₀ → σ j₀ = j₀ → ∀ k, w (σ⁻¹ k) = w k := by
    intro σ hσ0 hσ1 k
    have h1 : MulAut.conj (φ (permSU hM.field σ)) * f a₁ *
        (MulAut.conj (φ (permSU hM.field σ)))⁻¹ = f a₁ := by
      rw [← hfW _ ⟨σ, rfl⟩ a₁ ha₁H, hstab σ hσ0 hσ1]
    have h2 := hw.conj_perm hM.field σ
    rw [h1] at h2
    have h3 := hw.ratio_eq hM.field hd3 hM.ker h2 k i₀
    simp only [Equiv.Perm.inv_eq_iff_eq.mpr hσ0.symm] at h3
    exact (mul_right_cancel₀ (inv_ne_zero (hw.ne_zero i₀)) h3).symm
  have hw_out : ∀ k, k ≠ i₀ → k ≠ j₀ → w k = w k₂ := by
    intro k hki hkj
    by_cases hkk : k = k₂
    · rw [hkk]
    · have h := hbstab (Equiv.swap k k₂) (Equiv.swap_apply_of_ne_of_ne hki.symm hk0.symm)
        (Equiv.swap_apply_of_ne_of_ne hkj.symm hk1.symm) k
      rw [Equiv.swap_inv, Equiv.swap_apply_left] at h
      exact h.symm
  have hτa₁ : MulAut.conj (φ (permSU hM.field (Equiv.swap i₀ j₀))) * a₁ *
      (MulAut.conj (φ (permSU hM.field (Equiv.swap i₀ j₀))))⁻¹ = a₁⁻¹ := by
    have h1 : ActsDiagU φ (MulAut.conj (φ (permSU hM.field (Equiv.swap i₀ j₀))) * a₁ *
        (MulAut.conj (φ (permSU hM.field (Equiv.swap i₀ j₀))))⁻¹)
        (ggPairVec i₀ j₀ ζ ∘ ⇑(Equiv.swap i₀ j₀)⁻¹) := ha₁act.conj_perm hM.field _
    have e : ggPairVec i₀ j₀ ζ ∘ ⇑(Equiv.swap i₀ j₀)⁻¹ = fun m => (ggPairVec i₀ j₀ ζ m)⁻¹ := by
      rw [Equiv.swap_inv, ggPairVec_comp, Equiv.symm_swap, Equiv.swap_apply_left,
        Equiv.swap_apply_right, ggPairVec_swap]
    rw [e] at h1
    exact actsDiagU_unique hM.surj h1 (actsDiagU_inv ha₁act)
  have hbτ : MulAut.conj (φ (permSU hM.field (Equiv.swap i₀ j₀))) * f a₁ *
      (MulAut.conj (φ (permSU hM.field (Equiv.swap i₀ j₀))))⁻¹ = (f a₁)⁻¹ := by
    rw [← hfW _ ⟨Equiv.swap i₀ j₀, rfl⟩ a₁ ha₁H, hτa₁, hfinv a₁ ha₁H]
  have hw_sq : w k₂ * w k₂ = w i₀ * w j₀ := by
    have h2 := hw.conj_perm hM.field (Equiv.swap i₀ j₀)
    rw [hbτ] at h2
    have h3 := h2.ratio_eq hM.field hd3 hM.ker (actsDiagU_inv hw) k₂ i₀
    simp only [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hk0 hk1, Equiv.swap_apply_left,
      inv_inv] at h3
    have e1 := hw.ne_zero k₂
    have e2 := hw.ne_zero j₀
    field_simp at h3
    linear_combination h3
  obtain ⟨c, -, hc⟩ := hζ.eq_pow_of_pow_eq_one (hw.ratio_pow hM.field hd3 hM.ker hbp i₀ k₂)
  have hbeq : f a₁ = a₁ ^ c := by
    have h1 : ActsDiagU φ (a₁ ^ c) (fun k => ggPairVec i₀ j₀ ζ k ^ c) := ha₁act.pow c
    have h2 := actsDiagU_mul_const h1 (hw.ne_zero k₂)
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
    exact actsDiagU_unique hM.surj hw h2
  have hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ e ∈ H,
      ActsDiagU φ e (ggPairVec k l (ζ ^ m)) → f e = e ^ c := by
    intro k l hkl m e _ heE
    obtain ⟨ρ, hρk, hρl⟩ := exists_perm_pair hkl h01
    have hbm : ActsDiagU φ (a₁ ^ m) (ggPairVec i₀ j₀ (ζ ^ m)) := by
      have h1 := ha₁act.pow m
      rwa [ggPairVec_pow] at h1
    have hcj := hbm.conj_perm hM.field ρ⁻¹
    rw [inv_inv, show (fun k' => ggPairVec i₀ j₀ (ζ ^ m) (ρ k')) = ggPairVec k l (ζ ^ m) from
      ggPairVec_comp_of hρk hρl _] at hcj
    have heq : e = MulAut.conj (φ (permSU hM.field ρ⁻¹)) * (a₁ ^ m) *
        (MulAut.conj (φ (permSU hM.field ρ⁻¹)))⁻¹ := actsDiagU_unique hM.surj heE hcj
    rw [heq, hfW _ ⟨ρ⁻¹, rfl⟩ _ (H.pow_mem ha₁H m), hfpow a₁ ha₁H m, hbeq,
      show (a₁ ^ c) ^ m = (a₁ ^ m) ^ c by rw [← pow_mul, ← pow_mul, mul_comm]]
    exact conj_pow.symm
  have hP1 : f 1 = 1 ^ c := by rw [hf1, one_pow]
  have hPmul : ∀ a ∈ H, ∀ b ∈ H, f a = a ^ c → f b = b ^ c → f (a * b) = (a * b) ^ c := by
    intro a ha b hb hfa hfb
    rw [hfmul a ha b hb, hfa, hfb, Commute.mul_pow (hHcomm a ha b hb)]
  have hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ a ∈ H, ActsDiagU φ a t := by
    intro t ht htp
    obtain ⟨D, hD⟩ := exists_diagSU hM.field hpq ht htp
    exact ⟨_, Subgroup.subset_closure ⟨D, t, hD, ht, rfl⟩, actsDiagU_conj hD⟩
  refine ⟨c, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨D, u, hD, hu, rfl⟩ := hx
    have hDp : ∏ i, u i = 1 := by
      have h1 := ((mem_unitarySU_iff hM.field).mp D.2).1
      rwa [hD, det_diagonal] at h1
    obtain ⟨a', -, ha'P, ha'E⟩ := exists_actsDiagU_of_gen (A := H) hfull hζ hp (by omega)
      (fun e => f e = e ^ c) hP1 hPmul hPv hu hDp
    rw [actsDiagU_unique hM.surj (actsDiagU_conj hD) ha'E]
    exact ha'P
  | one => rw [hf1, one_pow]
  | mul x y hxm hym hx hy =>
    rw [hfmul x hxm y hym, hx, hy, Commute.mul_pow (hHcomm x hxm y hym)]
  | inv x hxm hx => rw [hfinv x hxm, hx, inv_pow]

end CFSG.StandardType.UnitAct

end
