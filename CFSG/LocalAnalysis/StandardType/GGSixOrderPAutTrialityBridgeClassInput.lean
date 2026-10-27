module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeClass

public section

namespace CFSG.StandardType

namespace TriBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.Triality CFSG.RankThree.PartTwo.Sec8

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem coe_bridge_conj_theta (γ z : Om8 K) :
    (bridge ((MulAut.conj γ * theta : MulAut (Om8 K)) z) : ModGL TwistTag.D4.tag K) =
      ((bridge γ : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K) * bridge z *
        ((bridge γ : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, coe_bridge_theta]
  group

theorem eq_one_of_commute_D4 {N : ModGL TwistTag.D4.tag K}
    (hN : N ∈ adjointGroup TwistTag.D4.tag K)
    (hc : ∀ w ∈ adjointGroup TwistTag.D4.tag K, N * w = w * N) : N = 1 := by
  have hz : (⟨N, hN⟩ : adjointGroup TwistTag.D4.tag K) ∈
      Subgroup.center (adjointGroup TwistTag.D4.tag K) := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (hc w.1 w.2).symm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem bridge_mul_diagramMap_pow_three {γ : Om8 K} (hβ : (MulAut.conj γ * theta) ^ 3 = 1) :
    ((bridge γ : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K) ^ 3 = 1 := by
  obtain ⟨b, hb⟩ : ∃ b, (bridge γ : ModGL TwistTag.D4.tag K) = b := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, diagramMap TwistTag.D4 K = P := ⟨_, rfl⟩
  have hbG : b ∈ adjointGroup TwistTag.D4.tag K := hb ▸ (bridge γ).2
  have hP3 : P ^ 3 = 1 := hP ▸ diagramMap_pow_order TwistTag.D4 K
  have hconj : ∀ w ∈ adjointGroup TwistTag.D4.tag K, P * w * P⁻¹ ∈ adjointGroup TwistTag.D4.tag K :=
    fun w hw => by
      rw [← hP, ← twistHom_id_eq]
      exact twistHom_mem_adjointGroup _ _ _ hw
  rw [hb, hP]
  refine eq_one_of_commute_D4 ?_ fun w hw => ?_
  · have e : (b * P) ^ 3 = b * (P * b * P⁻¹) * (P * (P * b * P⁻¹) * P⁻¹) * P ^ 3 := by
      rw [pow_three]
      group
    rw [e, hP3, mul_one]
    exact mul_mem (mul_mem hbG (hconj b hbG)) (hconj _ (hconj b hbG))
  · have hz : (bridge ((bridge (K := K)).symm ⟨w, hw⟩) : ModGL TwistTag.D4.tag K) = w := by
      rw [MulEquiv.apply_symm_apply]
    have h3 : (bridge (((MulAut.conj γ * theta : MulAut (Om8 K)) ^ 3)
        ((bridge (K := K)).symm ⟨w, hw⟩)) : ModGL TwistTag.D4.tag K) =
        (b * P) ^ 3 * w * ((b * P) ^ 3)⁻¹ := by
      rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, coe_bridge_conj_theta,
        coe_bridge_conj_theta, coe_bridge_conj_theta, hz, hb, hP, pow_three]
      group
    rw [hβ, MulAut.one_apply, hz] at h3
    calc (b * P) ^ 3 * w = ((b * P) ^ 3 * w * ((b * P) ^ 3)⁻¹) * (b * P) ^ 3 := by group
      _ = w * (b * P) ^ 3 := by rw [← h3]

theorem map_ggFix_eq_graphCentralizer {γ : Om8 K} {y : ModGL TwistTag.D4.tag K}
    (hy : y ∈ adjointGroup TwistTag.D4.tag K) :
    (ggFix (MulAut.conj γ * theta)).map ((MulAut.conj y).toMonoidHom.comp
        ((adjointGroup TwistTag.D4.tag K).subtype.comp (bridge (K := K)).toMonoidHom)) =
      graphCentralizer TwistTag.D4.tag K
        (y * ((bridge γ : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K)⁻¹ * y⁻¹) := by
  obtain ⟨b, hb⟩ : ∃ b, (bridge γ : ModGL TwistTag.D4.tag K) = b := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, diagramMap TwistTag.D4 K = P := ⟨_, rfl⟩
  have hβz : ∀ z, (bridge ((MulAut.conj γ * theta : MulAut (Om8 K)) z) :
      ModGL TwistTag.D4.tag K) = (b * P) * bridge z * (b * P)⁻¹ := by
    intro z
    rw [coe_bridge_conj_theta, hb, hP]
  rw [hb, hP]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (MulAut.conj γ * theta : MulAut (Om8 K)) z = z := hz
    have hc : (b * P) * (bridge z : ModGL TwistTag.D4.tag K) * (b * P)⁻¹ = bridge z := by
      rw [← hβz, hz']
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hy (bridge z).2) (inv_mem hy)
    · rw [mem_centralizer_singleton_iff_conj_eq]
      change (y * (b * P)⁻¹ * y⁻¹) * (y * (bridge z : ModGL TwistTag.D4.tag K) * y⁻¹) *
        (y * (b * P)⁻¹ * y⁻¹)⁻¹ = y * bridge z * y⁻¹
      calc (y * (b * P)⁻¹ * y⁻¹) * (y * (bridge z : ModGL TwistTag.D4.tag K) * y⁻¹) *
            (y * (b * P)⁻¹ * y⁻¹)⁻¹ =
            y * ((b * P)⁻¹ * (bridge z : ModGL TwistTag.D4.tag K) * (b * P)) * y⁻¹ := by group
        _ = y * ((b * P)⁻¹ * ((b * P) * (bridge z : ModGL TwistTag.D4.tag K) * (b * P)⁻¹) *
            (b * P)) * y⁻¹ := by rw [hc]
        _ = y * bridge z * y⁻¹ := by group
  · intro hw
    obtain ⟨hwG, hwc⟩ := Subgroup.mem_inf.1 hw
    rw [mem_centralizer_singleton_iff_conj_eq] at hwc
    have hmem : y⁻¹ * w * y ∈ adjointGroup TwistTag.D4.tag K :=
      mul_mem (mul_mem (inv_mem hy) hwG) hy
    refine ⟨(bridge (K := K)).symm ⟨y⁻¹ * w * y, hmem⟩, ?_, ?_⟩
    · change (MulAut.conj γ * theta : MulAut (Om8 K)) ((bridge (K := K)).symm
        ⟨y⁻¹ * w * y, hmem⟩) = (bridge (K := K)).symm ⟨y⁻¹ * w * y, hmem⟩
      apply (bridge (K := K)).injective
      apply Subtype.ext
      rw [hβz, MulEquiv.apply_symm_apply]
      change (b * P) * (y⁻¹ * w * y) * (b * P)⁻¹ = y⁻¹ * w * y
      calc (b * P) * (y⁻¹ * w * y) * (b * P)⁻¹ =
            y⁻¹ * (y * (b * P)⁻¹ * y⁻¹)⁻¹ * w * (y * (b * P)⁻¹ * y⁻¹) * y := by group
        _ = y⁻¹ * (y * (b * P)⁻¹ * y⁻¹)⁻¹ *
            ((y * (b * P)⁻¹ * y⁻¹) * w * (y * (b * P)⁻¹ * y⁻¹)⁻¹) *
              (y * (b * P)⁻¹ * y⁻¹) * y := by rw [hwc]
        _ = y⁻¹ * w * y := by group
    · change y * ((bridge ((bridge (K := K)).symm ⟨y⁻¹ * w * y, hmem⟩) :
        adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) * y⁻¹ = w
      rw [MulEquiv.apply_symm_apply]
      group

end TriBridge

namespace TriBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.Triality CFSG.RankThree.PartTwo.Sec8

theorem ggD4GraphClassPGLInput_of_second (h : GGD4SecondCentPGLInput) :
    GGD4GraphClassPGLInput := by
  intro K _ _ _ h3 γ hβ
  obtain ⟨b, hb⟩ : ∃ b, (bridge γ : ModGL TwistTag.D4.tag K) = b := ⟨_, rfl⟩
  have hbG : b ∈ adjointGroup TwistTag.D4.tag K := hb ▸ (bridge γ).2
  have hN : (b * diagramMap TwistTag.D4 K) ^ 3 = 1 := by
    rw [← hb]
    exact bridge_mul_diagramMap_pow_three hβ
  have hxG : (diagramMap TwistTag.D4 K)⁻¹ * b⁻¹ * diagramMap TwistTag.D4 K ∈
      adjointGroup TwistTag.D4.tag K := diagramMap_inv_conj_mem (inv_mem hbG)
  have hxs : (diagramMap TwistTag.D4 K)⁻¹ * b⁻¹ * diagramMap TwistTag.D4 K *
      (diagramMap TwistTag.D4 K)⁻¹ = (b * diagramMap TwistTag.D4 K)⁻¹ := by group
  have hx3 : ((diagramMap TwistTag.D4 K)⁻¹ * b⁻¹ * diagramMap TwistTag.D4 K *
      (diagramMap TwistTag.D4 K)⁻¹) ^ 3 = 1 := by
    rw [hxs, inv_pow, hN, inv_one]
  obtain ⟨y, hy, hcase⟩ := exists_conj_classes_D4 hxG hx3
  rw [hxs] at hcase
  rcases hcase with h1 | h2
  · left
    have hg : (bridge ((bridge (K := K)).symm ⟨y, hy⟩) : ModGL TwistTag.D4.tag K) = y := by
      rw [MulEquiv.apply_symm_apply]
    have hP' : y * (b * diagramMap TwistTag.D4 K) * y⁻¹ = diagramMap TwistTag.D4 K :=
      calc y * (b * diagramMap TwistTag.D4 K) * y⁻¹ =
            (y * (b * diagramMap TwistTag.D4 K)⁻¹ * y⁻¹)⁻¹ := by group
        _ = ((diagramMap TwistTag.D4 K)⁻¹)⁻¹ := by rw [h1]
        _ = diagramMap TwistTag.D4 K := inv_inv _
    set g := (bridge (K := K)).symm ⟨y, hy⟩ with hgdef
    have hconj : MulAut.conj g * (MulAut.conj γ * theta) * (MulAut.conj g)⁻¹ = theta := by
      refine MulEquiv.ext fun z => ?_
      apply (bridge (K := K)).injective
      apply Subtype.ext
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply,
        map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_bridge_conj_theta, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hg, hb, coe_bridge_theta]
      calc y * (b * diagramMap TwistTag.D4 K * (y⁻¹ * (bridge z : ModGL TwistTag.D4.tag K) * y) *
            (b * diagramMap TwistTag.D4 K)⁻¹) * y⁻¹ =
            (y * (b * diagramMap TwistTag.D4 K) * y⁻¹) * (bridge z : ModGL TwistTag.D4.tag K) *
              (y * (b * diagramMap TwistTag.D4 K) * y⁻¹)⁻¹ := by group
        _ = _ := by rw [hP']
    refine ⟨g⁻¹, ?_⟩
    rw [map_inv, inv_inv]
    calc MulAut.conj γ * theta = (MulAut.conj g)⁻¹ *
          (MulAut.conj g * (MulAut.conj γ * theta) * (MulAut.conj g)⁻¹) * MulAut.conj g := by
          group
      _ = _ := by rw [hconj]
  · right
    obtain ⟨e⟩ := h K h3
    have hmap := map_ggFix_eq_graphCentralizer (γ := γ) hy
    rw [hb, h2] at hmap
    have hinj : Function.Injective ((MulAut.conj y).toMonoidHom.comp
        ((adjointGroup TwistTag.D4.tag K).subtype.comp (bridge (K := K)).toMonoidHom)) :=
      (MulAut.conj y).injective.comp (Subtype.val_injective.comp (bridge (K := K)).injective)
    exact ⟨((ggFix (MulAut.conj γ * theta)).equivMapOfInjective _ hinj).trans
      ((MulEquiv.subgroupCongr hmap).trans e)⟩

end TriBridge

end CFSG.StandardType
