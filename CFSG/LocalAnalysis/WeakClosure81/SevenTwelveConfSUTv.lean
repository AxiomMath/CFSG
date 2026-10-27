module

public import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM
import CFSG.Quasithin.Vol2.Ch8Sec2L829NKLin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Open
open Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

open scoped Classical in
@[expose] noncomputable def suTv (hσ : IsUnitaryInvolution σ) (a : Fin m → F) (s : F) :
    ↥(SUid σ m) :=
  if h : herm σ a a = 0 ∧ s + σ s = 0 then tv hσ.invol h.1 h.2 else 1

theorem suTv_smul (hσ : IsUnitaryInvolution σ) {a : Fin m → F} (ha : herm σ a a = 0) {s : F}
    (hs : s + σ s = 0) (v : Fin m → F) :
    suTv hσ a s • v = v + (s * herm σ a v) • a := by
  rw [suTv, dif_pos ⟨ha, hs⟩, tv_smul]

theorem suTv_conj (hσ : IsUnitaryInvolution σ) (g : ↥(SUid σ m)) {a : Fin m → F}
    (ha : herm σ a a = 0) {s : F} (hs : s + σ s = 0) :
    g * suTv hσ a s * g⁻¹ = suTv hσ (g • a) s := by
  apply ext_smul
  intro v
  have ha' : herm σ (g • a) (g • a) = 0 := by rw [herm_smul_smul σ g a a, ha]
  rw [conj_smul_of_tv g (suTv hσ a s) (suTv_smul hσ ha hs) v, suTv_smul hσ ha' hs]

theorem suTv_smul_vec (hσ : IsUnitaryInvolution σ) {a : Fin m → F} (ha : herm σ a a = 0)
    {s : F} (hs : s + σ s = 0) (l : F) :
    suTv hσ (l • a) s = suTv hσ a (σ l * l * s) := by
  apply ext_smul
  intro v
  have ha' : herm σ (l • a) (l • a) = 0 := by
    rw [herm_smul_left, herm_smul_right, ha, mul_zero, mul_zero]
  have hs' : σ l * l * s + σ (σ l * l * s) = 0 := by
    have hσs : σ s = -s := by linear_combination hs
    rw [map_mul, map_mul, hσ.invol, hσs]
    ring
  rw [suTv_smul hσ ha' hs, suTv_smul hσ ha hs', herm_smul_left, smul_smul]
  have hscl : s * (σ l * herm σ a v) * l = σ l * l * s * herm σ a v := by ring
  rw [hscl]

theorem suTv_mul_suTv (hσ : IsUnitaryInvolution σ) {a : Fin m → F} (ha : herm σ a a = 0)
    {s s' : F} (hs : s + σ s = 0) (hs' : s' + σ s' = 0) :
    suTv hσ a s * suTv hσ a s' = suTv hσ a (s + s') := by
  apply ext_smul
  intro v
  have hss' : (s + s') + σ (s + s') = 0 := by
    rw [map_add]
    linear_combination hs + hs'
  rw [mul_smul, suTv_smul hσ ha hs, suTv_smul hσ ha hs', suTv_smul hσ ha hss']
  simp only [herm_add_right, herm_smul_right, ha, mul_zero, add_zero]
  module

variable {e : Fin m → F}

theorem suConf_two_le (he0 : e ≠ 0) (he : herm σ e e = 0) : 2 ≤ m := by
  by_contra hm
  have hm2 : m = 0 ∨ m = 1 := by omega
  rcases hm2 with rfl | rfl
  · exact he0 (Subsingleton.elim _ _)
  · apply he0
    funext i
    rw [Subsingleton.elim i 0]
    have h1 : σ (e 0) * e 0 = 0 := by
      simpa [herm, Fin.sum_univ_one] using he
    rcases mul_eq_zero.mp h1 with h | h
    · exact (map_eq_zero_iff σ σ.injective).mp h
    · exact h

private lemma suConfTv_one_add_sq {F : Type} [Field F] [CharP F 2] {m : ℕ}
    {N : Matrix (Fin m) (Fin m) F} (hN : N * N = 0) : (1 + N) * (1 + N) = 1 := by
  have h1 : (1 + N) * (1 + N) = 1 + N + (N + N * N) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  rw [h1, hN, add_zero, add_assoc, ← two_smul F N, CharTwo.two_eq_zero, zero_smul, add_zero]

private lemma suConfTv_normalForm {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (M : GL (Fin m) F)
    (hM : M ∈ SUid (unitaryInvolution F 2 n) m)
    (hr : (M.val - 1).rank = 1) :
    ∃ e : Fin m → F, e ≠ 0 ∧ herm (unitaryInvolution F 2 n) e e = 0 ∧
      M = ((suTv (isUnitaryInvolution_unitaryInvolution hF) e 1 :
        ↥(SUid (unitaryInvolution F 2 n) m)) : GL (Fin m) F) := by
  classical
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    rw [pow_zero, one_pow] at hF
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two
      one_le := hn
      card := by rw [hF, ← pow_mul, Nat.mul_comm] }
  have hdet : M.val.det = 1 := ((mem_SUid_iff (unitaryInvolution F 2 n)).mp hM).1
  obtain ⟨p, φ, hpφ⟩ :=
    CFSG.Quasithin.H13.L829NK.exists_vecMulVec_of_rank_le_one (M.val - 1) (le_of_eq hr)
  have hMval : M.val = 1 + Matrix.vecMulVec p φ := by
    rw [← hpφ, add_comm, sub_add_cancel]
  have hdetvec : (1 + Matrix.vecMulVec p φ).det = 1 + φ ⬝ᵥ p := by
    rw [Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : φ ⬝ᵥ p = 0 := by
    have h1 := hdet
    rw [hMval, hdetvec] at h1
    exact add_left_cancel (by rw [h1, add_zero])
  have hN2 : (M.val - 1) * (M.val - 1) = 0 := by
    rw [hpφ, Matrix.vecMulVec_mul_vecMulVec, hdot, zero_smul]
    simp
  have hMMval : M.val * M.val = 1 := by
    have h1 : M.val = 1 + (M.val - 1) := by rw [add_comm, sub_add_cancel]
    rw [h1, suConfTv_one_add_sq hN2]
  have hMM : M * M = 1 := Units.ext (by rw [Units.val_mul, hMMval, Units.val_one])
  have hMne : M ≠ 1 := by
    intro h
    have hrank : (M.val - 1).rank = 0 := by rw [h]; simp
    rw [hr] at hrank
    exact one_ne_zero hrank
  have hord : orderOf M = 2 := orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hMM) hMne
  have hmem : M ∈ StatedSU m (2 ^ n) F := by
    rw [← SUid_eq_statedSU hF m]
    exact hM
  obtain ⟨u, c, hu0, hc0, hcσ, huu, huc⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.URigid.exists_transvection_eq
      hdata hmem hord hr
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 n) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hσu : herm (unitaryInvolution F 2 n) u u = 0 := by
    rw [CFSG.ComponentClassification.RankTwoClassical.herm_eq_hform hdata u u, huu]
  have hbar : ∀ x : F, hdata.bar x = unitaryInvolution F 2 n x := by
    intro x
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, unitaryInvolution_apply]
  have hcσ' : unitaryInvolution F 2 n c = c := by
    rw [← hbar c]
    exact hcσ
  obtain ⟨μ, hμ⟩ := hσ.norm_surj c hcσ' hc0
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hμ
    exact hc0 hμ.symm
  have he0 : μ • u ≠ 0 := smul_ne_zero hμ0 hu0
  have he : herm (unitaryInvolution F 2 n) (μ • u) (μ • u) = 0 := by
    rw [herm_smul_left, herm_smul_right, hσu, mul_zero, mul_zero]
  have hMmat : M.val = 1 + c • Matrix.vecMulVec u (hdata.bar ∘ u) := by
    rw [← huc, add_comm, sub_add_cancel]
  have hmatsmul : ∀ v : Fin m → F,
      M.val *ᵥ v = v + herm (unitaryInvolution F 2 n) (μ • u) v • (μ • u) := by
    intro v
    have hdot' : (hdata.bar ∘ u) ⬝ᵥ v = herm (unitaryInvolution F 2 n) u v := by
      rw [CFSG.ComponentClassification.RankTwoClassical.herm_eq_hform hdata u v]
      rfl
    rw [hMmat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
    rw [hdot', herm_smul_left, smul_smul]
    have hs : c * herm (unitaryInvolution F 2 n) u v =
        (unitaryInvolution F 2 n μ * herm (unitaryInvolution F 2 n) u v) * μ := by
      rw [← hμ]
      ring
    rw [hs]
  have h1 : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have hact : ∀ v : Fin m → F, M.val *ᵥ v =
      (suTv (isUnitaryInvolution_unitaryInvolution hF) (μ • u) 1 :
        ↥(SUid (unitaryInvolution F 2 n) m)) • v := by
    intro v
    rw [suTv_smul hσ he h1]
    simpa using hmatsmul v
  refine ⟨μ • u, he0, he, ?_⟩
  refine Units.ext (Matrix.ext_iff_mulVec.mpr fun v => ?_)
  rw [hact v]
  rfl

theorem suConf_exists_tv {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (g : ↥(SUid (unitaryInvolution F 2 n) m))
    (hg : Matrix.rank (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) - 1) = 1) :
    ∃ e : Fin m → F, e ≠ 0 ∧ herm (unitaryInvolution F 2 n) e e = 0 ∧
      g = suTv (isUnitaryInvolution_unitaryInvolution hF) e 1 := by
  obtain ⟨e, he0, he, hge⟩ := suConfTv_normalForm hF (g : GL (Fin m) F) g.2 hg
  exact ⟨e, he0, he, Subtype.ext hge⟩

end CFSG.LocalAnalysis.WeakClosure81

end
