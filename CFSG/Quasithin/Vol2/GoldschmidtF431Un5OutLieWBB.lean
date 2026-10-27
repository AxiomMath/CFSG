module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieWB
public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base

public section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5
  CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5w_exists_omega (hf : 2 ≤ f) : ∃ ω : K, hK.bar ω = ω ∧ ω ≠ 0 ∧ ω ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : (hK.fixedField : Set K) ⊆ {0, 1} := by
    intro c hc
    have h1 := hcon c (hK.mem_fixedField.1 hc)
    by_cases h0 : c = 0
    · simp [h0]
    · simp [h1 h0]
  have hfin : Finite K := hK.finite
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : (({0, 1} : Set K)).ncard = 2 := Set.ncard_pair zero_ne_one
  have h4 : (hK.fixedField : Set K).ncard = 2 ^ f := by
    rw [← Nat.card_coe_set_eq]
    exact hK.card_fixedField
  rw [h3, h4] at h2
  have h5 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem un5w_mem_spTf {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    {g : hypSU hK 2 1} (hg : g ∈ hypUnitriangular hK 2 1)
    (hfix : fieldAut hK (bar5 hK) g = g) : innM hK g ∈ spTf T (fieldP hK (bar5 hK)) := by
  refine ⟨hU (Subgroup.mem_map_of_mem _ hg), ?_⟩
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact un5w_fieldP_comm_innM hK _ hfix

theorem un5w_z_central {T : Subgroup (MulAut (hypPSU hK 2 1))}
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) {τ : MulAut (hypPSU hK 2 1)}
    (hτ : τ ∈ T) : τ * innM hK (z₁SU hK) = innM hK (z₁SU hK) * τ := by
  obtain ⟨u, hu, σ, rfl⟩ := hT τ hτ
  obtain ⟨g, hg, rfl⟩ := hu
  have h1 : innM hK g * innM hK (z₁SU hK) = innM hK (z₁SU hK) * innM hK g := by
    rw [← map_mul, ← map_mul, (ZPsub_commute z₁SU_mem_ZPsub hg).symm]
  have h2 := un5w_fieldP_comm_innM hK σ (un5w_fieldAut_z₁SU hK σ)
  calc innM hK g * fieldP hK σ * innM hK (z₁SU hK)
      = innM hK g * (fieldP hK σ * innM hK (z₁SU hK)) := mul_assoc _ _ _
    _ = innM hK g * (innM hK (z₁SU hK) * fieldP hK σ) := by rw [h2]
    _ = innM hK g * innM hK (z₁SU hK) * fieldP hK σ := (mul_assoc _ _ _).symm
    _ = innM hK (z₁SU hK) * innM hK g * fieldP hK σ := by rw [h1]
    _ = innM hK (z₁SU hK) * (innM hK g * fieldP hK σ) := mul_assoc _ _ _

theorem un5w_mem_spTf_lev {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T) {s : K}
    (hs : hK.bar s = s) :
    innM hK (lev (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s)) ∈
      spTf T (fieldP hK (bar5 hK)) :=
  un5w_mem_spTf hK hU (un5w_lev_mem hK s) (un5w_fieldAut_lev hK hs)

theorem un5w_mem_spTf_vSU {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T) {t : K}
    (ht : hK.bar t = t) :
    innM hK (vSU hK !![0, 0; 0, t] (un5w_isHerm hK ht)) ∈ spTf T (fieldP hK (bar5 hK)) :=
  un5w_mem_spTf hK hU (Ssub_le_Usub (Vsub_le_Ssub (vSU_mem_Vsub _)))
    (un5w_fieldAut_vSU hK _ _ (fun i j => by
      fin_cases i <;> fin_cases j <;> simp [fld5_bar_apply, ht]))

theorem un5w_z_mem_comm (hf : 2 ≤ f) {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T) :
    innM hK (z₁SU hK) ∈
      ⁅spTf T (fieldP hK (bar5 hK)), spTf T (fieldP hK (bar5 hK))⁆ := by
  obtain ⟨ω, hω, hω0, hω1⟩ := un5w_exists_omega hK hf
  have h2 := un5w_two hK
  have hne : ω ^ 2 + ω ≠ 0 := by
    intro h
    have : ω * (ω + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hω0 h'
    · exact hω1 (by linear_combination h' - h2)
  have hb1 : hK.bar (1 : K) = 1 := map_one _
  have hb2 : hK.bar ((ω ^ 2 + ω)⁻¹) = (ω ^ 2 + ω)⁻¹ := by simp [hω]
  have hb3 : hK.bar (ω * (ω ^ 2 + ω)⁻¹) = ω * (ω ^ 2 + ω)⁻¹ := by simp [hω]
  have key := un5w_comm_prod hK hb1 hb3 hω hb2 (s₁ := 1) (t₁ := ω * (ω ^ 2 + ω)⁻¹)
    (s₂ := ω) (t₂ := (ω ^ 2 + ω)⁻¹)
    (by linear_combination mul_inv_cancel₀ hne) (by linear_combination (ω * (ω ^ 2 + ω)⁻¹) * h2)
  rw [← key, map_mul, map_commutatorElement, map_commutatorElement]
  exact mul_mem
    (Subgroup.commutator_mem_commutator (un5w_mem_spTf_lev hK hU hb1)
      (un5w_mem_spTf_vSU hK hU hb3))
    (Subgroup.commutator_mem_commutator (un5w_mem_spTf_lev hK hU hω)
      (un5w_mem_spTf_vSU hK hU hb2))

theorem un5_W_ne (hf : 2 ≤ f) {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ)
    (hb : fieldP hK (bar5 hK) ∈ T) :
    ∃ x ∈ spWf T (fieldP hK (bar5 hK)), x ∈ (ZPsub hK).map (innM hK) ∧ x ≠ 1 := by
  have _ := hb
  have hzU : z₁SU hK ∈ hypUnitriangular hK 2 1 := ZPsub_le_U z₁SU_mem_ZPsub
  have hz : innM hK (z₁SU hK) ∈ spTf T (fieldP hK (bar5 hK)) :=
    un5w_mem_spTf hK hU hzU (un5w_fieldAut_z₁SU hK _)
  refine ⟨innM hK (z₁SU hK), ⟨⟨hz, ?_⟩, un5w_z_mem_comm hK hf hU⟩,
    Subgroup.mem_map_of_mem _ z₁SU_mem_ZPsub, fun hz1 => z₁SU_ne_one (h := hK) ?_⟩
  · refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact un5w_z_central hK hT hy.1
  · exact innM_injOn (Sec53F.Unit.u5_center_eq_bot hK) hzU (one_mem _)
      (hz1.trans (map_one _).symm)

end CFSG.Quasithin.H13.F431.Un.OL5
