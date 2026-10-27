module

public import CFSG.RankThree.GF2n.Parrott.CaseIIHvLift
public import CFSG.RankThree.GF2n.Parrott.CaseIIHvLFt
public import CFSG.RankThree.GF2n.Parrott.SpinHvChecks
public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Local
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "QP" => QP45.originalSubgroup.subgroupOf QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

private theorem v_not_mem_QP :
    vA ∉ QP := by
  rw [Subgroup.mem_subgroupOf]
  exact v_not_mem_Q

variable {G : Type} [Group G] [Finite G] {z : G}

theorem not_isConj_z_of_v_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hnouv : ∀ (a : G) (ha : a ∈ H z), IsConj (qH D ⟨a, ha⟩) (uA * vA) → a * a ≠ 1) :
    ∀ (a : G) (ha : a ∈ H z), a * a = 1 → IsConj (qH D ⟨a, ha⟩) vA → ¬ IsConj z a := by
  intro a haH haa hq hza
  obtain ⟨c, hca⟩ := isConj_iff.mp hza
  have hz2 : orderOf z = 2 := orderOf_z_A h
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro hz
    rw [hz, orderOf_one] at hz2
    norm_num at hz2
  have haz : a * z = z * a := mem_centralizer_singleton_iff.mp haH
  obtain ⟨κ₀, hκ₀⟩ := exists_isSpinCoord_A h D hIII
  obtain ⟨g, hg⟩ := isConj_iff.mp hq
  have hκ := hκ₀.transport g
  set ψ : ↥(H z) →* A45 := (MulAut.conj g).toMonoidHom.comp (qH D) with hψ
  have hψy : ∀ w : ↥(H z), ψ w = g * qH D w * g⁻¹ := fun w => rfl
  have hψa : ψ ⟨a, haH⟩ = vA := by rw [hψy, hg]
  obtain ⟨x, hxH, hψx, hxa, hxx⟩ := hκ.exists_commuting_lift hzz vUV_mul_self vUVG₁_commute
    vUVG₂_commute commutator_vUVG_mul_vUV rhoA_v_fixed_mem_range exists_rhoA_v_fixed_q_eq_one
    rhoA_vUV_fixed_mem_range rhoA_vUV_fixed_singular rhoA_v_vUV_fixed_mem_image haH haa hψa
  have hxz : x * x = z := by
    refine hxx.resolve_left fun hx1 => hnouv x hxH ?_ hx1
    refine IsConj.trans (isConj_iff.mpr ⟨g, ?_⟩) isConj_vUV
    rw [← hψx, hψy]
  set y : G := c⁻¹ * z * c with hy
  have hyH : y ∈ H z := by
    rw [H, mem_centralizer_singleton_iff]
    calc y * z = c⁻¹ * (z * (c * z * c⁻¹)) * c := by rw [hy]; group
      _ = c⁻¹ * ((c * z * c⁻¹) * z) * c := by rw [hca, haz]
      _ = z * y := by rw [hy]; group
  have hyy : y * y = 1 := by
    calc y * y = c⁻¹ * (z * z) * c := by rw [hy]; group
      _ = 1 := by rw [hzz]; group
  have hy1 : y ≠ 1 := by
    intro h1
    apply hz1
    calc z = c * y * c⁻¹ := by rw [hy]; group
      _ = 1 := by rw [h1]; group
  have hv1 : vA ≠ 1 := fun h1 => v_not_mem_QP (h1 ▸ Subgroup.one_mem _)
  have hyz : y ≠ z := by
    intro h1
    have hcz : c * z = z * c := by
      calc c * z = c * y := by rw [h1]
        _ = z * c := by rw [hy]; group
    have haz' : a = z := by
      rw [← hca, hcz]
      group
    have haJ : a ∈ J z := by
      rw [haz']
      exact z_mem_J_A h
    have hq1 : qH D ⟨a, haH⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr haJ)
    rw [hq1, mul_one, mul_inv_cancel] at hg
    exact hv1 hg.symm
  set x' : G := c⁻¹ * x * c with hx'
  have hx'H : x' ∈ H z := by
    rw [H, mem_centralizer_singleton_iff]
    calc x' * z = c⁻¹ * (x * (c * z * c⁻¹)) * c := by rw [hx']; group
      _ = c⁻¹ * ((c * z * c⁻¹) * x) * c := by rw [hca, hxa]
      _ = z * x' := by rw [hx']; group
  have hx'x' : x' * x' = y := by
    calc x' * x' = c⁻¹ * (x * x) * c := by rw [hx']; group
      _ = y := by rw [hxz]
  have hyQP : qH D ⟨y, hyH⟩ ∈ QP := by
    have e : (⟨y, hyH⟩ : ↥(H z)) = ⟨x', hx'H⟩ * ⟨x', hx'H⟩ := Subtype.ext hx'x'.symm
    rw [e, map_mul]
    exact Subgroup.mul_self_mem_of_index_two index_QP45 _
  by_cases hyJ : y ∈ J z
  ·
    refine not_isConj_z_of_mem_J_A h D hIII y hyJ
      (orderOf_eq_prime (by rw [sq]; exact hyy) hy1) ?_
      (isConj_iff.mpr ⟨c⁻¹, by rw [hy, inv_inv]⟩)
    intro hyz'
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hyz' with h1 | h1
    · exact hy1 h1
    · exact hyz h1
  · have hq1 : qH D ⟨y, hyH⟩ ≠ 1 := fun h1 =>
      hyJ (Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1))
    have hqy2 : orderOf (qH D ⟨y, hyH⟩) = 2 := by
      refine orderOf_eq_prime ?_ hq1
      rw [sq, ← map_mul]
      have e : (⟨y, hyH⟩ : ↥(H z)) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
      rw [e, map_one]
    rcases qa45_involution_classes _ hqy2 with ht | hut | hv | huv
    ·
      obtain ⟨g', hg'⟩ := isConj_iff.mp ht
      have hκt := hκ₀.transport g'
      obtain ⟨u₁, u₂, u₃, u₄, h1, h2, h3, h4, h12, h34, h13, h14, h23, h24⟩ :=
        rhoA_t_hyperbolic_pairs
      have ht' : ((MulAut.conj g').toMonoidHom.comp (qH D)) ⟨y, hyH⟩ = tA := hg'
      rw [← ht'] at h1 h2 h3 h4
      have hLF := hκt.z_mem_commutator_centralizer_of_fixed hzz hyH h1 h2 h3 h4 h12 h34 h13 h14
        h23 h24
      have hpart := CFSG.GroupTheory.mul_mul_inv_mem_commutator_centralizer_of_mem (z := z)
        (g := c) hLF
      rw [hca] at hpart
      exact not_mem_commutator_of_qH_not_mem_QP45 D haH
        (not_mem_QP45_of_isConj hq v_not_mem_QP) hpart
    ·
      have hax : a * x ∈ H z := mul_mem haH hxH
      have hψax : ψ ⟨a * x, hax⟩ = vA * vUV := by
        have e : (⟨a * x, hax⟩ : ↥(H z)) = ⟨a, haH⟩ * ⟨x, hxH⟩ := rfl
        rw [e, map_mul, hψa, hψx]
      have haxx : (a * x) * (a * x) = z := by
        calc (a * x) * (a * x) = a * (x * a) * x := by group
          _ = (a * a) * (x * x) := by rw [hxa]; group
          _ = z := by rw [haa, hxz, one_mul]
      have hyc : IsConj (ψ ⟨y, hyH⟩) (vA * vUV) := by
        refine IsConj.trans ?_ (hut.trans isConj_v_mul_vUV.symm)
        exact isConj_iff.mpr ⟨g⁻¹, by rw [hψy]; group⟩
      exact hκ.mul_self_ne_one_of_isConj hzz hz1 rhoA_v_mul_vUV_fixed_mem_range hax hψax haxx hyH
        hyc hyy
    ·
      exact not_mem_QP45_of_isConj hv v_not_mem_QP hyQP
    ·
      exact not_mem_QP45_of_isConj huv uv_not_mem_QP45 hyQP

theorem parrott_lemma36_caseII (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ z ∈ G₀ ∧ H z ⊓ G₀ = ⁅H z, H z⁆ :=
  exists_index_two_inf_eq_commutator_A_of_hv h D hIII (not_isConj_z_of_v_A h D hIII)

end CFSG.RankThree.GF2n.Parrott
