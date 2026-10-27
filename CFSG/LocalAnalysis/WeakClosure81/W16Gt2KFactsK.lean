module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsJ
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Quasithin (conjSubgroup)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem exists_isotropic_perp_pair (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (hm : 4 ≤ m)
    {e f : Fin m → F} (he : herm (unitaryInvolution F 2 n) e e = 0)
    (hf : herm (unitaryInvolution F 2 n) f f = 0) (hef : herm (unitaryInvolution F 2 n) e f = 1) :
    ∃ c : Fin m → F, c ≠ 0 ∧ herm (unitaryInvolution F 2 n) c c = 0 ∧
      herm (unitaryInvolution F 2 n) c e = 0 ∧ herm (unitaryInvolution F 2 n) c f = 0 := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨z₁, hz₁, hz₁e, hz₁f⟩ := exists_norm_one_perp_pair hσ (by omega : 3 ≤ m) he hf hef
  have hz₁e' : herm σ z₁ e = 0 := herm_eq_zero_comm σ hσ.invol hz₁e
  have hz₁f' : herm σ z₁ f = 0 := herm_eq_zero_comm σ hσ.invol hz₁f
  obtain ⟨z₂, hz₂, hz₁z₂, hez₂, hfz₂⟩ :=
    exists_norm_one_perp_three hσ hm hz₁ he hf hef hz₁e' hz₁f'
  have hz₂z₁ : herm σ z₂ z₁ = 0 := herm_eq_zero_comm σ hσ.invol hz₁z₂
  have hz₂e' : herm σ z₂ e = 0 := herm_eq_zero_comm σ hσ.invol hez₂
  have hz₂f' : herm σ z₂ f = 0 := herm_eq_zero_comm σ hσ.invol hfz₂
  refine ⟨z₁ + z₂, ?_, ?_, ?_, ?_⟩
  · intro h0
    have h1 : herm σ (z₁ + z₂) z₁ = 0 := by rw [h0, herm_zero_left]
    rw [herm_add_left, hz₁, hz₂z₁, add_zero] at h1
    exact one_ne_zero h1
  · rw [herm_add_left, herm_add_right, herm_add_right, hz₁, hz₂, hz₁z₂, hz₂z₁, add_zero, zero_add]
    exact CharTwo.add_self_eq_zero 1
  · rw [herm_add_left, hz₁e', hz₂e', add_zero]
  · rw [herm_add_left, hz₁f', hz₂f', add_zero]

private theorem suTv_tau_smul (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e f : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) (hf : herm (unitaryInvolution F 2 n) f f = 0)
    (hef : herm (unitaryInvolution F 2 n) e f = 1) {ν : F} (hν0 : ν ≠ 0)
    (hν : ν + unitaryInvolution F 2 n ν = 0) :
    ((suTv (isUnitaryInvolution_unitaryInvolution hF) e ν *
        suTv (isUnitaryInvolution_unitaryInvolution hF) f ν⁻¹ *
        suTv (isUnitaryInvolution_unitaryInvolution hF) e ν) *
      (suTv (isUnitaryInvolution_unitaryInvolution hF) e 1 *
        suTv (isUnitaryInvolution_unitaryInvolution hF) f 1 *
        suTv (isUnitaryInvolution_unitaryInvolution hF) e 1)⁻¹) • e = ν • e := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hfe : herm σ f e = 1 := by rw [herm_conj σ hσ.invol, hef, map_one]
  have h2e : e + e = 0 := by rw [← two_smul F e, CharTwo.two_eq_zero, zero_smul]
  have h2f : f + f = 0 := by rw [← two_smul F f, CharTwo.two_eq_zero, zero_smul]
  have h11 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hσν : σ ν = ν := by
    have h : σ ν = -ν := by linear_combination hν
    rw [h, CharTwo.neg_eq]
  have hνi : ν⁻¹ + σ ν⁻¹ = 0 := by
    rw [map_inv₀, hσν]
    exact CharTwo.add_self_eq_zero _
  have hinv1 : ∀ a : Fin m → F, herm σ a a = 0 → (suTv hσ a 1)⁻¹ = suTv hσ a 1 := by
    intro a ha
    apply inv_eq_of_mul_eq_one_right
    rw [suTv_mul_suTv hσ ha h11 h11, CharTwo.add_self_eq_zero (1 : F)]
    exact kFacts_suTv_zero_param hF ha
  have s1 : suTv hσ e 1 • e = e := by
    rw [suTv_smul hσ he h11, he, mul_zero, zero_smul, add_zero]
  have s2 : suTv hσ f 1 • e = e + f := by
    rw [suTv_smul hσ hf h11, hfe, mul_one, one_smul]
  have s3 : suTv hσ e 1 • (e + f) = f := by
    rw [suTv_smul hσ he h11, herm_add_right, he, hef, zero_add, mul_one, one_smul,
      add_comm e f, add_assoc, h2e, add_zero]
  have hV : (suTv hσ e 1 * (suTv hσ f 1 * suTv hσ e 1)) • e = f := by
    rw [mul_smul, mul_smul, s1, s2, s3]
  have t1 : suTv hσ e ν • f = f + ν • e := by
    rw [suTv_smul hσ he hν, hef, mul_one]
  have t2 : suTv hσ f ν⁻¹ • (f + ν • e) = ν • e := by
    rw [suTv_smul hσ hf hνi, herm_add_right, herm_smul_right, hf, hfe, zero_add, mul_one,
      inv_mul_cancel₀ hν0, one_smul, add_comm f (ν • e), add_assoc, h2f, add_zero]
  have t3 : suTv hσ e ν • (ν • e) = ν • e := by
    rw [suTv_smul hσ he hν, herm_smul_right, he, mul_zero, mul_zero, zero_smul, add_zero]
  rw [mul_inv_rev, mul_inv_rev, hinv1 e he, hinv1 f hf, mul_smul, hV, mul_smul, mul_smul, t1, t2,
    t3]

private theorem mem_conjSubgroup_iff_exists_kFactsSuProjTv (hF : Nat.card F = (2 ^ n) ^ 2)
    {m : ℕ} {A : Subgroup (StatedProj (StatedSU m (2 ^ n) F))} {e c : Fin m → F}
    (hc : herm (unitaryInvolution F 2 n) c c = 0) (t : ↥(SUid (unitaryInvolution F 2 n) m))
    (ht : t • c = e)
    (hA : ∀ x : StatedProj (StatedSU m (2 ^ n) F), x ∈ A ↔
      ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧ x = kFactsSuProjTv hF m e s)
    (x : StatedProj (StatedSU m (2 ^ n) F)) :
    x ∈ conjSubgroup A (kFactsSuProj hF m t) ↔
      ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧ x = kFactsSuProjTv hF m c s := by
  rw [CFSG.Quasithin.mem_conjSubgroup_iff, hA]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    have h := kFacts_suProj_conj_suProjTv hF t hc hs
    rw [ht] at h
    exact mul_left_cancel (mul_right_cancel (hx.trans h.symm))
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [kFacts_suProj_conj_suProjTv hF t hc hs, ht]

theorem kFacts_su_config :
    ∀ (m n : ℕ) (F : Type) [Field F] [Finite F], 4 ≤ m → 2 ≤ n →
      Nat.card F = (2 ^ n) ^ 2 →
      ∀ A B : Subgroup (StatedProj (StatedSU m (2 ^ n) F)), Nat.card A = 2 ^ n →
        Nat.card B = 2 ^ n →
        (∀ x ∈ A, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n x) →
        (∀ x ∈ B, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n x) →
        ¬ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
          ∃ γ τ, τ ∈ A ⊔ B ∧ conjSubgroup A γ ≠ A ∧
            (∀ x ∈ conjSubgroup A γ, ∀ y ∈ A ⊔ B, x * y = y * x) ∧
            τ ∈ Subgroup.normalizer (A : Set _) ∧ (∀ a ∈ A, τ * a = a * τ → a = 1) := by
  intro m n F _ _ hm hn hF A B hA hB hAt hBt hnc
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨e, f, he, hf, hef, hAe, hBf⟩ :=
    kFacts_su_hyperbolic_pair hF hn hm A B hA hB hAt hBt hnc
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hef
    exact zero_ne_one hef
  obtain ⟨c, hc0, hc, hce, hcf⟩ := exists_isotropic_perp_pair hF hm he hf hef
  have hce' : herm σ e c = 0 := herm_eq_zero_comm σ hσ.invol hce
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ (by omega : 3 ≤ m) hc0 hc he0 he
  have hconj := mem_conjSubgroup_iff_exists_kFactsSuProjTv hF hc t ht hAe
  obtain ⟨ν, hνσ, hν0, hν1, -⟩ := exists_zech_unitary hF (by omega : 1 < n)
  have hνtr : ν + σ ν = 0 := by rw [hνσ]; exact CharTwo.add_self_eq_zero ν
  have h11 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hνitr : ν⁻¹ + σ ν⁻¹ = 0 := by
    rw [map_inv₀, hνσ]; exact CharTwo.add_self_eq_zero _
  have hAmem : ∀ s : F, s + σ s = 0 → kFactsSuProjTv hF m e s ∈ A :=
    fun s hs => (hAe _).mpr ⟨s, hs, rfl⟩
  have hBmem : ∀ s : F, s + σ s = 0 → kFactsSuProjTv hF m f s ∈ B :=
    fun s hs => (hBf _).mpr ⟨s, hs, rfl⟩
  have hA' : ∀ s : F, s + σ s = 0 → kFactsSuProjTv hF m e s ∈ A ⊔ B :=
    fun s hs => Subgroup.mem_sup_left (hAmem s hs)
  have hB' : ∀ s : F, s + σ s = 0 → kFactsSuProjTv hF m f s ∈ A ⊔ B :=
    fun s hs => Subgroup.mem_sup_right (hBmem s hs)
  set τ₀ : ↥(SUid σ m) :=
    (suTv hσ e ν * suTv hσ f ν⁻¹ * suTv hσ e ν) *
      (suTv hσ e 1 * suTv hσ f 1 * suTv hσ e 1)⁻¹ with hτ₀
  have hτ₀e : τ₀ • e = ν • e := suTv_tau_smul hF he hf hef hν0 hνtr
  set τ : StatedProj (StatedSU m (2 ^ n) F) := kFactsSuProj hF m τ₀ with hτdef
  have hτmem : τ ∈ A ⊔ B := by
    have h : τ = (kFactsSuProjTv hF m e ν * kFactsSuProjTv hF m f ν⁻¹ *
        kFactsSuProjTv hF m e ν) * (kFactsSuProjTv hF m e 1 * kFactsSuProjTv hF m f 1 *
        kFactsSuProjTv hF m e 1)⁻¹ := by
      rw [hτdef, hτ₀]
      unfold kFactsSuProjTv
      simp only [map_mul, map_inv]
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hA' ν hνtr)
      (hB' ν⁻¹ hνitr)) (hA' ν hνtr)) (Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hA' 1 h11) (hB' 1 h11)) (hA' 1 h11)))
  have hνν : σ ν * ν = ν * ν := by rw [hνσ]
  have hννtr : ∀ s : F, s + σ s = 0 → ν * ν * s + σ (ν * ν * s) = 0 := by
    intro s hs
    rw [map_mul, map_mul, hνσ]
    calc ν * ν * s + ν * ν * σ s = ν * ν * (s + σ s) := by ring
      _ = 0 := by rw [hs, mul_zero]
  have hτconj : ∀ s : F, s + σ s = 0 →
      τ * kFactsSuProjTv hF m e s * τ⁻¹ = kFactsSuProjTv hF m e (ν * ν * s) := by
    intro s hs
    rw [hτdef, kFacts_suProj_conj_suProjTv hF τ₀ he hs, hτ₀e,
      kFacts_suProjTv_smul_vec hF he hs ν, hνν]
  refine ⟨kFactsSuProj hF m t, τ, hτmem, ?_, ?_, ?_, ?_⟩
  · intro hAeq
    have h1 : kFactsSuProjTv hF m c 1 ∈ conjSubgroup A (kFactsSuProj hF m t) :=
      (hconj _).mpr ⟨1, h11, rfl⟩
    rw [hAeq] at h1
    obtain ⟨μ, hμ⟩ := kFacts_su_smul_of_mem hF hm A hAt he0 he hc0 hc (hAmem 1 h11) h1
    have h2 : herm σ c f = 0 := hcf
    rw [hμ, herm_smul_left, hef, mul_one] at h2
    have h3 : μ = 0 := (map_eq_zero_iff σ σ.injective).mp h2
    exact hc0 (by rw [hμ, h3, zero_smul])
  · intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := (hconj x).mp hx
    have hle : A ⊔ B ≤ Subgroup.centralizer {kFactsSuProjTv hF m c s} := by
      refine sup_le ?_ ?_
      · intro z hz
        obtain ⟨t', ht', rfl⟩ := (hAe z).mp hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (kFacts_suProjTv_comm_of_herm_eq_zero hF hc he hce hs ht').symm
      · intro z hz
        obtain ⟨t', ht', rfl⟩ := (hBf z).mp hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (kFacts_suProjTv_comm_of_herm_eq_zero hF hc hf hcf hs ht').symm
    have h := hle hy
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h.symm
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨s, hs, rfl⟩ := (hAe z).mp hz
      rw [hτconj s hs]
      exact hAmem _ (hννtr s hs)
    · intro hz
      obtain ⟨t', ht', ht''⟩ := (hAe _).mp hz
      have hν2 : ν * ν ≠ 0 := mul_ne_zero hν0 hν0
      have hfix : σ (ν * ν) = ν * ν := by rw [map_mul, hνσ]
      have htr2 : (ν * ν)⁻¹ * t' + σ ((ν * ν)⁻¹ * t') = 0 := by
        rw [map_mul, map_inv₀, hfix]
        calc (ν * ν)⁻¹ * t' + (ν * ν)⁻¹ * σ t' = (ν * ν)⁻¹ * (t' + σ t') := by ring
          _ = 0 := by rw [ht', mul_zero]
      have h5 : τ * z * τ⁻¹ = τ * kFactsSuProjTv hF m e ((ν * ν)⁻¹ * t') * τ⁻¹ := by
        rw [ht'', hτconj _ htr2, mul_inv_cancel_left₀ hν2]
      have h6 : z = kFactsSuProjTv hF m e ((ν * ν)⁻¹ * t') :=
        mul_left_cancel (mul_right_cancel h5)
      rw [h6]
      exact hAmem _ htr2
  · intro z hz hcomm
    obtain ⟨s, hs, rfl⟩ := (hAe z).mp hz
    have h7 : τ * kFactsSuProjTv hF m e s * τ⁻¹ = kFactsSuProjTv hF m e s := by
      rw [hcomm, mul_inv_cancel_right]
    rw [hτconj s hs] at h7
    have h8 := kFacts_suProjTv_injective hF he0 he (hννtr s hs) hs h7
    have hνν1 : ν * ν ≠ 1 := by
      intro h
      rcases mul_self_eq_one_iff.mp h with h | h
      · exact hν1 h
      · exact hν1 (by rw [h, CharTwo.neg_eq])
    have h9 : (ν * ν - 1) * s = 0 := by
      rw [sub_mul, h8, one_mul, sub_self]
    rcases mul_eq_zero.mp h9 with h | h
    · exact absurd (sub_eq_zero.mp h) hνν1
    · rw [h]
      unfold kFactsSuProjTv
      rw [kFacts_suTv_zero_param hF he, map_one]

end CFSG.LocalAnalysis.WeakClosure81
