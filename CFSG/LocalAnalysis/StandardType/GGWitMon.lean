module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

open Subgroup

private def wMon_subgroup {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) : Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {a | ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j}
  mul_mem' := by
    intro a b ha hb i
    obtain ⟨j, c', hc', hbj⟩ := hb i
    obtain ⟨k, c, hc, hak⟩ := ha j
    refine ⟨k, c' * c, mul_ne_zero hc' hc, ?_⟩
    rw [LinearEquiv.mul_apply, hbj, map_smul, hak, smul_smul]
  one_mem' := by
    intro i
    refine ⟨i, 1, one_ne_zero, ?_⟩
    simp
  inv_mem' := by
    intro a ha
    choose φ c h using ha
    have hc : ∀ i, c i ≠ 0 := fun i => (h i).1
    have hφ : ∀ i, a (f i) = c i • f (φ i) := fun i => (h i).2
    have hinj : Function.Injective φ := by
      intro i₁ i₂ hij
      by_contra hne
      have h1 : f i₁ = c i₁ • a⁻¹ (f (φ i₁)) := by
        calc f i₁ = a⁻¹ (a (f i₁)) := by simp
          _ = a⁻¹ (c i₁ • f (φ i₁)) := by rw [hφ i₁]
          _ = c i₁ • a⁻¹ (f (φ i₁)) := by simp
      have h2 : f i₂ = c i₂ • a⁻¹ (f (φ i₂)) := by
        calc f i₂ = a⁻¹ (a (f i₂)) := by simp
          _ = a⁻¹ (c i₂ • f (φ i₂)) := by rw [hφ i₂]
          _ = c i₂ • a⁻¹ (f (φ i₂)) := by simp
      have hrel : c i₂ • f i₁ = c i₁ • f i₂ := by
        rw [h1, h2, show a⁻¹ (f (φ i₁)) = a⁻¹ (f (φ i₂)) by rw [hij],
          smul_smul, smul_smul, mul_comm]
      have hrepr : c i₂ • f.equivFun (f i₁) = c i₁ • f.equivFun (f i₂) := by
        simpa using congrArg f.equivFun hrel
      have heval := congrArg (fun x : Fin n → ZMod p => x i₁) hrepr
      simp [Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul, Ne.symm hne] at heval
      exact hc i₂ heval
    intro k
    obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective).mp hinj k
    refine ⟨i, (c i)⁻¹, inv_ne_zero (hc i), ?_⟩
    have h1 : f i = c i • a⁻¹ (f k) := by
      calc f i = a⁻¹ (a (f i)) := by simp
        _ = a⁻¹ (c i • f k) := by rw [hφ i, hi]
        _ = c i • a⁻¹ (f k) := by simp
    rw [h1, smul_smul, inv_mul_cancel₀ (hc i), one_smul]

private theorem wMon_permMap_apply {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permMap p f σ (f i) = f (σ i) := by
  rw [permMap, Module.Basis.equiv_apply]

private theorem wMon_permMap_mem {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (σ : Equiv.Perm (Fin n)) :
    permMap p f σ ∈ wMon_subgroup f := by
  intro i
  exact ⟨σ i, 1, one_ne_zero, by rw [wMon_permMap_apply, one_smul]⟩

private theorem wMon_diagMap_apply {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ) (i : Fin n) :
    diagMap p f d (f i) = ((d i : (ZMod p)ˣ) : ZMod p) • f i := by
  unfold diagMap
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  have hX : (LinearEquiv.piCongrRight fun j => LinearEquiv.smulOfUnit (d j))
      (f.equivFun (f i)) = Pi.single i ((d i : (ZMod p)ˣ) : ZMod p) := by
    funext j
    rw [LinearEquiv.piCongrRight_apply]
    by_cases h : i = j
    · subst h
      simp [Module.Basis.equivFun_self, LinearEquiv.smulOfUnit, Units.smul_def, smul_eq_mul,
        mul_one]
    · simp [Module.Basis.equivFun_self, LinearEquiv.smulOfUnit, h]
  rw [hX, Module.Basis.equivFun_symm_apply, Fintype.sum_eq_single i]
  · simp
  · intro j hj
    simp [Pi.single_eq_of_ne hj]

private theorem wMon_diagMap_mem {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ) :
    diagMap p f d ∈ wMon_subgroup f := by
  intro i
  exact ⟨i, (d i : ZMod p), Units.ne_zero (d i), wMon_diagMap_apply f d i⟩

private theorem wMon_val_ne_one {p : ℕ} (ζ : (ZMod p)ˣ) (h2 : 2 ≤ orderOf ζ) :
    (ζ : ZMod p) ≠ 1 := by
  intro hc
  have hne : ζ ≠ 1 := by
    intro hunit
    rw [hunit] at h2
    rw [orderOf_one] at h2
    omega
  exact hne (Units.ext hc)

private theorem wMon_val_ne_neg_one {p : ℕ} (ζ : (ZMod p)ˣ) (h3 : 3 ≤ orderOf ζ) :
    (ζ : ZMod p) ≠ -1 := by
  intro hc
  have hunit : ζ = -1 := Units.ext hc
  have h2 : ζ ^ 2 = 1 := by rw [hunit]; norm_num
  have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hle : orderOf ζ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem wit_gmmn_mon {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (hn : 3 ≤ n) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ)
    (m : ℕ) (h01 : i₀ ≠ i₁) (hm : 3 ≤ m) (hζ : orderOf ζ = m) :
    WitMON p (gmmn p f i₀ i₁ ζ) := by
  have h3 : 3 ≤ orderOf ζ := by rw [hζ]; exact hm
  have hle : gmmn p f i₀ i₁ ζ ≤ wMon_subgroup f := by
    apply (closure_le (wMon_subgroup f)).mpr
    rintro a (ha | ha)
    · rcases ha with ⟨σ, rfl⟩
      exact wMon_permMap_mem f σ
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact wMon_diagMap_mem f (pairUnit p i₀ i₁ ζ)
  refine ⟨n, f, hn, ?_, ?_⟩
  · intro a ha i
    exact hle ha i
  · refine ⟨diagMap p f (pairUnit p i₀ i₁ ζ), ?_, ?_, ?_⟩
    · exact subset_closure (by simp)
    · intro i
      exact ⟨((pairUnit p i₀ i₁ ζ i : (ZMod p)ˣ) : ZMod p),
        wMon_diagMap_apply f (pairUnit p i₀ i₁ ζ) i⟩
    · refine ⟨i₀, (ζ : ZMod p), ?_, wMon_val_ne_one ζ (le_trans (by norm_num) h3),
        wMon_val_ne_neg_one ζ h3⟩
      rw [wMon_diagMap_apply f (pairUnit p i₀ i₁ ζ) i₀]
      simp [pairUnit]

theorem wit_g2mmn_mon {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (hn : 3 ≤ n) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ)
    (m : ℕ) (h01 : i₀ ≠ i₁) (hm : 2 ≤ m) (hζ : orderOf ζ = 2 * m) :
    WitMON p (g2mmn p f i₀ i₁ ζ) := by
  have h3 : 3 ≤ orderOf ζ := by rw [hζ]; omega
  have hle : g2mmn p f i₀ i₁ ζ ≤ wMon_subgroup f := by
    apply (closure_le (wMon_subgroup f)).mpr
    rintro a (ha | ha)
    · rcases ha with ⟨σ, rfl⟩
      exact wMon_permMap_mem f σ
    · rcases ha with ha | ha
      · rw [ha]
        exact wMon_diagMap_mem f (fun i => if i = i₀ then -1 else 1)
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact wMon_diagMap_mem f (pairUnit p i₀ i₁ ζ)
  refine ⟨n, f, hn, ?_, ?_⟩
  · intro a ha i
    exact hle ha i
  · refine ⟨diagMap p f (pairUnit p i₀ i₁ ζ), ?_, ?_, ?_⟩
    · exact subset_closure (by simp)
    · intro i
      exact ⟨((pairUnit p i₀ i₁ ζ i : (ZMod p)ˣ) : ZMod p),
        wMon_diagMap_apply f (pairUnit p i₀ i₁ ζ) i⟩
    · refine ⟨i₀, (ζ : ZMod p), ?_, wMon_val_ne_one ζ (le_trans (by norm_num) h3),
        wMon_val_ne_neg_one ζ h3⟩
      rw [wMon_diagMap_apply f (pairUnit p i₀ i₁ ζ) i₀]
      simp [pairUnit]

end CFSG.StandardType.ZS

end
