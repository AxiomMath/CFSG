module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsH
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem kFacts_su_exists_centre (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {x : StatedProj (StatedSU m (2 ^ n) F)} (hx : IsUnitaryTransvectionIn m n x) :
    ∃ e : Fin m → F, e ≠ 0 ∧ herm (unitaryInvolution F 2 n) e e = 0 ∧
      x = kFactsSuProjTv hF m e 1 := by
  obtain ⟨g, rfl, hg⟩ := hx
  obtain ⟨e, he0, he, hge⟩ := suConf_exists_tv hF
    ((MulEquiv.subgroupCongr (SUid_eq_statedSU hF m)).symm g) hg
  refine ⟨e, he0, he, ?_⟩
  unfold kFactsSuProjTv
  rw [← hge]
  unfold kFactsSuProj
  simp

private theorem suTv_zero_vec (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} :
    suTv (isUnitaryInvolution_unitaryInvolution hF) (0 : Fin m → F) (1 : F) = 1 := by
  apply ext_smul
  intro v
  have h1 : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]; exact CharTwo.add_self_eq_zero 1
  rw [suTv_smul _ (herm_zero_left _ 0) h1, smul_zero, add_zero, one_smul]

theorem kFacts_suTv_zero_param (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) :
    suTv (isUnitaryInvolution_unitaryInvolution hF) e (0 : F) = 1 := by
  apply ext_smul
  intro v
  rw [suTv_smul _ he (by simp), zero_mul, zero_smul, add_zero, one_smul]

theorem kFacts_su_smul_of_mem (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (hm : 4 ≤ m)
    (A : Subgroup (StatedProj (StatedSU m (2 ^ n) F)))
    (hAt : ∀ x ∈ A, x ≠ 1 → IsUnitaryTransvectionIn m n x)
    {e e' : Fin m → F} (he0 : e ≠ 0) (he : herm (unitaryInvolution F 2 n) e e = 0)
    (he0' : e' ≠ 0) (he' : herm (unitaryInvolution F 2 n) e' e' = 0)
    (hx : kFactsSuProjTv hF m e 1 ∈ A) (hy : kFactsSuProjTv hF m e' 1 ∈ A) :
    ∃ μ : F, e' = μ • e := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  by_contra hne
  have hne' : ∀ μ : F, e' ≠ μ • e := fun μ h => hne ⟨μ, h⟩
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  set P : ↥(SUid σ m) := suTv hσ e 1 * suTv hσ e' 1 with hP
  have hz : kFactsSuProj hF m P ∈ A := by
    have h : kFactsSuProj hF m P = kFactsSuProjTv hF m e 1 * kFactsSuProjTv hF m e' 1 := by
      unfold kFactsSuProjTv
      rw [hP, map_mul]
    rw [h]
    exact A.mul_mem hx hy
  obtain ⟨e'', he'', hzz⟩ : ∃ e'' : Fin m → F, herm σ e'' e'' = 0 ∧
      kFactsSuProj hF m P = kFactsSuProjTv hF m e'' 1 := by
    by_cases hz1 : kFactsSuProj hF m P = 1
    · refine ⟨0, herm_zero_left σ 0, ?_⟩
      rw [hz1]
      unfold kFactsSuProjTv
      rw [suTv_zero_vec hF, map_one]
    · obtain ⟨e'', -, he'', h⟩ := kFacts_su_exists_centre hF (hAt _ hz hz1)
      exact ⟨e'', he'', h⟩
  have hzz' : kFactsSuProj hF m P = kFactsSuProj hF m (suTv hσ e'' 1) := hzz
  obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF P (suTv hσ e'' 1)).mp hzz'
  have heq : ∀ v : Fin m → F, suTv hσ e'' 1 • v = (u : F) • (P • v) := by
    intro v
    rw [smul_def, smul_def, hu, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Matrix.mulVec_smul _ _ _
  have hPv : ∀ v : Fin m → F, P • v =
      v + herm σ e' v • e' + (herm σ e v + herm σ e' v * herm σ e e') • e := by
    intro v
    rw [hP, mul_smul, suTv_smul hσ he' h1, suTv_smul hσ he h1]
    simp only [one_mul, herm_add_right, herm_smul_right]
    module
  have heq' : ∀ v : Fin m → F, v + herm σ e'' v • e'' = (u : F) •
      (v + herm σ e' v • e' + (herm σ e v + herm σ e' v * herm σ e e') • e) := by
    intro v
    have h := heq v
    rw [hPv, suTv_smul hσ he'' h1, one_mul] at h
    exact h
  obtain ⟨w₁, hw₁e, hw₁e'⟩ := kFacts_exists_herm_eq_pair hF he0 hne' 1 0
  obtain ⟨w₂, hw₂e, hw₂e'⟩ := kFacts_exists_herm_eq_pair hF he0 hne' 0 1
  by_cases hu1 : (u : F) = 1
  · have e1 := heq' w₁
    have e2 := heq' w₂
    rw [hu1, one_smul, hw₁e, hw₁e'] at e1
    rw [hu1, one_smul, hw₂e, hw₂e'] at e2
    have k1 : herm σ e'' w₁ • e'' = e := by linear_combination (norm := module) e1
    have k2 : herm σ e'' w₂ • e'' = e' + herm σ e e' • e := by
      linear_combination (norm := module) e2
    have hc : herm σ e'' w₁ ≠ 0 := by
      intro h
      rw [h, zero_smul] at k1
      exact he0 k1.symm
    generalize herm σ e'' w₁ = K₁ at k1 hc
    generalize herm σ e'' w₂ = K₂ at k2
    generalize herm σ e e' = c₀ at k2
    have h3 : e'' = K₁⁻¹ • e := by rw [← k1, inv_smul_smul₀ hc]
    have h4 : e' = K₂ • e'' - c₀ • e := by rw [k2]; abel
    exact hne' (K₂ * K₁⁻¹ - c₀) (by rw [h4, h3, smul_smul, sub_smul])
  · have hu1' : (1 : F) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    let S : Submodule F (Fin m → F) := Submodule.span F (Set.range ![e'', e', e])
    have hmem : ∀ v : Fin m → F, v ∈ S := by
      intro v
      have h := heq' v
      have hv : (1 - (u : F)) • v = (-(herm σ e'' v)) • e'' + ((u : F) * herm σ e' v) • e' +
          ((u : F) * (herm σ e v + herm σ e' v * herm σ e e')) • e := by
        linear_combination (norm := module) h
      have h5 : v = (1 - (u : F))⁻¹ • ((1 - (u : F)) • v) := by rw [inv_smul_smul₀ hu1']
      rw [h5, hv]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)
    have htop : (⊤ : Submodule F (Fin m → F)) ≤ S := fun v _ => hmem v
    have h6 := Submodule.finrank_mono htop
    rw [finrank_top, Module.finrank_fin_fun] at h6
    have h7 : Module.finrank F S ≤ Fintype.card (Fin 3) :=
      finrank_range_le_card (R := F) ![e'', e', e]
    rw [Fintype.card_fin] at h7
    omega

theorem kFacts_su_rootGroup (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) {m : ℕ} (hm : 4 ≤ m)
    (A : Subgroup (StatedProj (StatedSU m (2 ^ n) F))) (hA : Nat.card A = 2 ^ n)
    (hAt : ∀ x ∈ A, x ≠ 1 → IsUnitaryTransvectionIn m n x) :
    ∃ e : Fin m → F, e ≠ 0 ∧ herm (unitaryInvolution F 2 n) e e = 0 ∧
      ∀ x : StatedProj (StatedSU m (2 ^ n) F), x ∈ A ↔
        ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧ x = kFactsSuProjTv hF m e s := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra hcon
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr fun x hx => by
      by_contra h
      exact hcon ⟨x, hx, h⟩
    rw [hbot, Subgroup.card_bot] at hA
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e, he0, he, rfl⟩ := kFacts_su_exists_centre hF (hAt x₀ hx₀ hx₀1)
  refine ⟨e, he0, he, ?_⟩
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hsub : ∀ x ∈ A, ∃ s : F, s + σ s = 0 ∧ x = kFactsSuProjTv hF m e s := by
    intro x hx
    by_cases hx1 : x = 1
    · refine ⟨0, by simp, ?_⟩
      rw [hx1]
      unfold kFactsSuProjTv
      rw [kFacts_suTv_zero_param hF he, map_one]
    · obtain ⟨e', he0', he', rfl⟩ := kFacts_su_exists_centre hF (hAt x hx hx1)
      obtain ⟨μ, rfl⟩ := kFacts_su_smul_of_mem hF hm A hAt he0 he he0' he' hx₀ hx
      refine ⟨σ μ * μ * 1, ?_, kFacts_suProjTv_smul_vec hF he h1 μ⟩
      have h2 : σ (σ μ * μ * 1) = σ μ * μ * 1 := by
        rw [mul_one, map_mul, hσ.invol, mul_comm]
      rw [h2]
      exact CharTwo.add_self_eq_zero _
  intro x
  refine ⟨hsub x, fun hx => ?_⟩
  let f : {s : F // s + σ s = 0} → StatedProj (StatedSU m (2 ^ n) F) :=
    fun s => kFactsSuProjTv hF m e s.1
  have hinj : Function.Injective f := by
    intro s s' h
    exact Subtype.ext (kFacts_suProjTv_injective hF he0 he s.2 s'.2 h)
  have hsubset : (A : Set (StatedProj (StatedSU m (2 ^ n) F))) ⊆ Set.range f := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := hsub z hz
    exact ⟨⟨s, hs⟩, rfl⟩
  have hcard : (Set.range f).ncard ≤ (A : Set (StatedProj (StatedSU m (2 ^ n) F))).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
    change Nat.card {s : F // s + σ s = 0} ≤ Nat.card A
    rw [hA, kFacts_card_traceZero hF]
  have heq := Set.eq_of_subset_of_ncard_le hsubset hcard (Set.finite_range _)
  obtain ⟨s, hs, hxs⟩ := hx
  have hmem : x ∈ Set.range f := ⟨⟨s, hs⟩, hxs.symm⟩
  rw [← heq] at hmem
  exact hmem

end CFSG.LocalAnalysis.WeakClosure81
