module

public import CFSG.LocalAnalysis.StandardType.GGResIDefs
public import CFSG.LocalAnalysis.StandardType.GGResIIWitness

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Witness

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {R : Type} [CommRing R] {φ : R →+* ZMod p} {N : ℕ}
  {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {α : Fin N → Module.Dual (ZMod p) V}
  {g : Fin N → (V ≃ₗ[ZMod p] V)}

@[expose] def ggFH (T : Fin N → Vector R (N + 1)) (t : Fin N × List (Fin N)) : Vector R (N + 1) :=
  ggFWord T t.2 (ggFUnit t.1.castSucc)

theorem ggFPi_zero (z : Vector R (N + 1)) :
    ggFPi φ h 0 z = ∑ l : Fin N, φ (z.get l.castSucc) • h l := by
  rw [ggFPi, smul_zero, add_zero]

theorem ggFPi_zero_comb (a b : ZMod p) (z₁ z₂ : Vector R (N + 1)) :
    a • ggFPi φ h 0 z₁ - b • ggFPi φ h 0 z₂ =
      ∑ l : Fin N, (a * φ (z₁.get l.castSucc) - b * φ (z₂.get l.castSucc)) • h l := by
  rw [ggFPi_zero, ggFPi_zero, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, smul_smul, sub_smul]

theorem ggF_tvH (hp2 : p ≠ 2) (hT : GGFTable φ T h 0 α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (t₁ t₂ : Fin N × List (Fin N)) (l₀ : Fin (N + 1))
    (z : Vector R (N + 1))
    (hZ : ∀ l : Fin N, φ ((ggFH T t₂).get l₀ * (ggFH T t₁).get l.castSucc -
      (ggFH T t₁).get l₀ * (ggFH T t₂).get l.castSucc) = 0)
    (hn : φ ((ggFH T t₁).get l₀) ≠ 0) (hd : φ ((ggFH T t₂).get l₀) ≠ 0)
    (hY : φ ((ggFH T t₁).get l₀ * ggFRootAt T (ggFC T t₁) z -
      (ggFH T t₂).get l₀ * ggFRootAt T (ggFC T t₂) z) ≠ 0) :
    ∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ v, t (t v - v) = t v - v := by
  set H₁ := ggFPi φ h 0 (ggFH T t₁)
  set H₂ := ggFPi φ h 0 (ggFH T t₂)
  set A₁ := ggFFun φ α (ggFC T t₁)
  set A₂ := ggFFun φ α (ggFC T t₂)
  set ln := φ ((ggFH T t₁).get l₀)
  set ld := φ ((ggFH T t₂).get l₀)
  have hprop : ld • H₁ = ln • H₂ := by
    rw [← sub_eq_zero, ggFPi_zero_comb]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← map_mul, ← map_mul, ← RingHom.map_sub, hZ l, zero_smul]
  have hH₂ : H₂ = (ld / ln) • H₁ := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, hprop, smul_smul, inv_mul_cancel₀ hn, one_smul]
  let β : Module.Dual (ZMod p) V := (ld / ln) • A₂
  have hconj₁ : ∀ v, ((t₁.2.map g).prod * g t₁.1 * ((t₁.2.map g).prod)⁻¹) v = v - A₁ v • H₁ :=
    ggF_conj' hT hg h2 t₁
  have hconj₂ : ∀ v, ((t₂.2.map g).prod * g t₂.1 * ((t₂.2.map g).prod)⁻¹) v = v - β v • H₁ := by
    intro v
    rw [ggF_conj' hT hg h2 t₂]
    change v - A₂ v • H₂ = v - ((ld / ln) * A₂ v) • H₁
    rw [hH₂, smul_smul, mul_comm]
  have hA₁ : A₁ H₁ = 2 := ggF_root_coroot hT hg h2 t₁
  have hβ : β H₁ = 2 := by
    have h22 : A₂ H₂ = 2 := ggF_root_coroot hT hg h2 t₂
    have hH₁ : H₁ = (ln / ld) • H₂ := by
      rw [div_eq_mul_inv, mul_comm, mul_smul, ← hprop, smul_smul, inv_mul_cancel₀ hd, one_smul]
    change (ld / ln) * A₂ H₁ = 2
    rw [hH₁, map_smul, smul_eq_mul, h22]
    field_simp
  have hne : A₁ ≠ β := by
    intro heq
    have hv := congrArg (fun f : Module.Dual (ZMod p) V => f (ggFPi φ h 0 z)) heq
    simp only [β, LinearMap.smul_apply, smul_eq_mul, A₁, A₂, ggFFun_pi hT] at hv
    apply hY
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hv]
    field_simp
    ring
  exact ⟨_, Subgroup.mul_mem _ (ggF_conj_mem t₁.1 t₁.2) (ggF_conj_mem t₂.1 t₂.2),
    ggResII_tv_of_coroot hp2 hconj₁ hconj₂ hA₁ hβ hne⟩

theorem ggF_dual_ext_of_span (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤)
    {A B : Module.Dual (ZMod p) V} (hAB : ∀ l, A (h l) = B (h l)) : A = B := by
  apply LinearMap.ext_on_range hspan
  exact hAB

theorem ggF_tvkV (hp2 : p ≠ 2) (hT : GGFTable φ T h 0 α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤)
    (hind : LinearIndependent (ZMod p) h) (t₁ t₂ : Fin N × List (Fin N)) (o₀ l : Fin N)
    (hroot : ∀ o : Fin N, φ (ggFDualAt T (ggFC T t₂) o₀ * ggFDualAt T (ggFC T t₁) o -
      ggFDualAt T (ggFC T t₁) o₀ * ggFDualAt T (ggFC T t₂) o) = 0)
    (_hn : φ (ggFDualAt T (ggFC T t₂) o₀) ≠ 0) (hd : φ (ggFDualAt T (ggFC T t₁) o₀) ≠ 0)
    (hco : φ (ggFDualAt T (ggFC T t₁) o₀ * (ggFH T t₁).get l.castSucc -
      ggFDualAt T (ggFC T t₂) o₀ * (ggFH T t₂).get l.castSucc) ≠ 0) :
    ∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ v, t (t v - v) = t v - v := by
  set H₁ := ggFPi φ h 0 (ggFH T t₁)
  set H₂ := ggFPi φ h 0 (ggFH T t₂)
  set A₁ := ggFFun φ α (ggFC T t₁)
  set A₂ := ggFFun φ α (ggFC T t₂)
  set mn := φ (ggFDualAt T (ggFC T t₂) o₀)
  set md := φ (ggFDualAt T (ggFC T t₁) o₀)
  have hA : mn • A₁ = md • A₂ := by
    apply ggF_dual_ext_of_span hspan
    intro o
    simp only [LinearMap.smul_apply, smul_eq_mul, A₁, A₂, ggFFun_coroot hT]
    rw [← map_mul, ← map_mul, ← sub_eq_zero, ← RingHom.map_sub]
    exact hroot o
  have hA' : ∀ v, A₂ v = (mn / md) * A₁ v := by
    intro v
    have hv := congrArg (fun f : Module.Dual (ZMod p) V => f v) hA
    simp only [LinearMap.smul_apply, smul_eq_mul] at hv
    field_simp
    linear_combination -hv
  set H₂' := (mn / md) • H₂
  have hconj₁ : ∀ v, ((t₁.2.map g).prod * g t₁.1 * ((t₁.2.map g).prod)⁻¹) v = v - A₁ v • H₁ :=
    ggF_conj' hT hg h2 t₁
  have hconj₂ : ∀ v, ((t₂.2.map g).prod * g t₂.1 * ((t₂.2.map g).prod)⁻¹) v = v - A₁ v • H₂' := by
    intro v
    rw [ggF_conj' hT hg h2 t₂]
    change v - A₂ v • H₂ = v - A₁ v • ((mn / md) • H₂)
    rw [hA', smul_smul, mul_comm]
  have hA₁ : A₁ H₁ = 2 := ggF_root_coroot hT hg h2 t₁
  have hA₁' : A₁ H₂' = 2 := by
    rw [map_smul, smul_eq_mul]
    have h22 : A₂ H₂ = 2 := ggF_root_coroot hT hg h2 t₂
    rw [hA' H₂] at h22
    exact h22
  have hne : H₁ ≠ H₂' := by
    intro heq
    apply hco
    have h0 : md • H₁ - mn • H₂ = 0 := by
      rw [heq, smul_smul, div_eq_mul_inv, mul_comm mn, ← mul_assoc, mul_inv_cancel₀ hd,
        one_mul, sub_self]
    rw [ggFPi_zero_comb] at h0
    have hc := (Fintype.linearIndependent_iff.mp hind) _ h0 l
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul]
    exact hc
  exact ⟨_, Subgroup.mul_mem _ (ggF_conj_mem t₁.1 t₁.2) (ggF_conj_mem t₂.1 t₂.2),
    ggResII_tv_of_root hp2 hconj₁ hconj₂ hA₁ hA₁' hne⟩

theorem ggF_triMat_eq (hT : GGFTable φ T h 0 α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (j j' : Fin N) (ws : List (Fin N)) :
    ggTriMat (α j) (α j') ((α j).comp (((ws.map g).prod)⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap)
        (h j) (h j') ((ws.map g).prod (h j)) =
      fun i k => φ (![![(T j).get j.castSucc, (T j).get j'.castSucc, ggFA T (j, ws) j],
        ![(T j').get j.castSucc, (T j').get j'.castSucc, ggFA T (j, ws) j'],
        ![ggFDualAt T (ggFC T (j, ws)) j, ggFDualAt T (ggFC T (j, ws)) j',
          ggFDualAt T (ggFC T (j, ws)) j * 0 + 2]] i k) := by
  have hH : (ws.map g).prod (h j) = ggFPi φ h 0 (ggFWord T ws (ggFUnit j.castSucc)) := by
    rw [← ggFPi_unit (φ := φ) h 0 j, ggFPi_word hT hg]
  have hA : (α j).comp (((ws.map g).prod)⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap =
      ggFFun φ α (ggFC T (j, ws)) := by
    ext w
    rw [ggFC, ← ggFFun_word hT hg, ← ggF_word_inv hg h2, ggFFun_unit]
    rfl
  funext i k
  fin_cases i <;> fin_cases k <;>
    simp only [ggTriMat, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hA, hH]
  · exact hT.1 j j
  · exact hT.1 j j'
  · exact ggFA_spec hT (j, ws) j
  · exact hT.1 j' j
  · exact hT.1 j' j'
  · exact ggFA_spec hT (j, ws) j'
  · exact ggFFun_coroot hT _ j
  · exact ggFFun_coroot hT _ j'
  · rw [← hH, ← hA]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, h2 j, mul_zero, zero_add, map_ofNat]

end Witness

end CFSG.StandardType
