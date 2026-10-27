module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma45Aux
public import CFSG.GroupTheory.CentralInvolutionIndexFour
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndCentralizer
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem centralizer_eq_top_of_lemma44 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hfuse : ∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z)
    (h44 : ∀ y ∈ ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁, orderOf y = 2 → IsConj z₁ y → y = z₁)
    (hH' : (⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁).relIndex (H z) = 2)
    (hG₀ : ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ ¬ H z ≤ G₀)
    (hO : ∃ t' j₀ : G, orderOf t' = 2 ∧ IsConj z t' ∧ j₀ ∈ J z ∧ j₀ ∉ centerIn (J z) ∧
      IsConj (t' * z) j₀)
    (hB5 : ∀ G₀ : Subgroup G, G₀.Normal → G₀.index = 2 → z ∈ G₀ → z₁ ∉ G₀ →
      (∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∃ G₁ : Subgroup G, G₁ ≤ G₀ ∧ G₁.relIndex G₀ = 2 ∧
        (∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
        ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥G₁ ≃* X)) :
    centralizer ({z₁} : Set G) = ⊤ := by
  obtain ⟨G₀, hG₀n, hG₀i, hHG₀⟩ := hG₀
  have hz2 : orderOf z = 2 := h.1
  have hcomm : ∀ a b : G, ⁅a, b⁆ ∈ G₀ := by
    intro a b
    rw [commutatorElement_def]
    simp only [Subgroup.mul_mem_iff_of_index_two hG₀i, inv_mem_iff]
    tauto
  have hH'G₀ : ⁅H z, H z⁆ ≤ G₀ := Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
  have hzG₀ : z ∈ G₀ := by
    have h1 : z ∈ ⁅J z, J z⁆ := by
      rw [show ⁅J z, J z⁆ = Subgroup.zpowers z from h.2.2.1]
      exact Subgroup.mem_zpowers z
    exact hH'G₀ (Subgroup.commutator_mono (J_le_H (z := z)) (J_le_H (z := z)) h1)
  have hz₁H : H z ≤ centralizer ({z₁} : Set G) := by
    intro x hx
    have hz₁' : z₁ ∈ centerIn (H z) := hZ ▸ hz₁
    rw [mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hz₁'.2 x hx
  obtain ⟨h₀, hh₀H, hh₀⟩ := SetLike.not_le_iff_exists.mp hHG₀
  have hrel : G₀.relIndex (H z) = 2 := by
    have h1 : G₀.relIndex (H z) ≤ G₀.relIndex ⊤ :=
      Subgroup.relIndex_le_of_le_right le_top (by rw [Subgroup.relIndex_top_right, hG₀i]; omega)
    rw [Subgroup.relIndex_top_right, hG₀i] at h1
    have h2 : G₀.relIndex (H z) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact hHG₀
    have h3 : G₀.relIndex (H z) ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card G₀ (H z)
      rw [h0] at this
      have hpos : 0 < Nat.card (H z) := Nat.card_pos
      omega
    omega
  by_cases hz₁G₀ : z₁ ∈ G₀
  ·
    have hPQ : ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁ ≤ H z ⊓ G₀ :=
      sup_le (le_inf (Subgroup.commutator_le_self _) hH'G₀)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨J_le_H (hz₁.1), hz₁G₀⟩))
    have hQH : (H z ⊓ G₀).relIndex (H z) = 2 := by
      rw [Subgroup.inf_relIndex_left]
      exact hrel
    have hQP : H z ⊓ G₀ ≤ ⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁ := by
      have h1 := Subgroup.relIndex_mul_relIndex (⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁) (H z ⊓ G₀)
        (H z) hPQ inf_le_left
      rw [hQH, hH'] at h1
      have h2 : (⁅H z, H z⁆ ⊔ Subgroup.zpowers z₁).relIndex (H z ⊓ G₀) = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp h2
    obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z)
    have hJT : J z ≤ T := J_le_of_isSylowOf T hT
    have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isSylowOf_H h hZ T hT
    have hwc : ∀ g : G, g * z₁ * g⁻¹ ∈ T → g * z₁ * g⁻¹ = z₁ := by
      intro g hg
      have hyH : g * z₁ * g⁻¹ ∈ H z := hT.le hg
      have hyG₀ : g * z₁ * g⁻¹ ∈ G₀ := hG₀n.conj_mem z₁ hz₁G₀ g
      have hord : orderOf (g * z₁ * g⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hz₁2
      exact h44 _ (hQP (Subgroup.mem_inf.mpr ⟨hyH, hyG₀⟩)) hord (isConj_iff.mpr ⟨g, rfl⟩)
    have hsup := eq_centralizer_sup_pPrimeCore_of_weakly_closed hTtop hz₁2 (hJT hz₁.1) hwc
    obtain ⟨t', j₀, ht', hzt', hj₀, hj₀c, hconj⟩ := hO
    rw [pPrimeCore_eq_bot_of_fusion h ht' hzt' hj₀ hj₀c hconj, sup_bot_eq] at hsup
    exact hsup
  ·
    have hfuse₀ : ∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z := by
      obtain ⟨g, -, hgH, hgz⟩ := hfuse
      have hh₀z : h₀ * z = z * h₀ := mem_centralizer_singleton_iff.mp hh₀H
      have hconj : (g * h₀) * z * (g * h₀)⁻¹ = g * z * g⁻¹ := by
        calc (g * h₀) * z * (g * h₀)⁻¹ = g * (h₀ * z * h₀⁻¹) * g⁻¹ := by group
          _ = g * z * g⁻¹ := by rw [hh₀z]; group
      by_cases hgG₀ : g ∈ G₀
      · exact ⟨g, hgG₀, hgH, hgz⟩
      · refine ⟨g * h₀, ?_, hconj ▸ hgH, hconj ▸ hgz⟩
        exact (Subgroup.mul_mem_iff_of_index_two hG₀i).mpr (iff_of_false hgG₀ hh₀)
    obtain ⟨G₁, hG₁G₀, hG₁i, hC, X, _, hX, ⟨e⟩⟩ := hB5 G₀ hG₀n hG₀i hzG₀ hz₁G₀ hfuse₀
    have hXs : IsSimpleGroup X :=
      (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _
        (hX.statedClassicalModel (by decide))).2
    have hsimple : IsSimpleGroup G₁ := e.isSimpleGroup
    have hG₀card : Nat.card G₀ = 2 * Nat.card G₁ := by
      have h1 := Subgroup.relIndex_mul_card G₁ G₀
      rw [inf_eq_left.mpr hG₁G₀, hG₁i] at h1
      omega
    have hbig : 2 < Nat.card G₁ := by
      have h1 := Subgroup.relIndex_mul_card G₀ (H z)
      rw [hrel] at h1
      have h2 : Nat.card (G₀ ⊓ H z : Subgroup G) ≤ Nat.card G₀ :=
        Subgroup.card_le_of_le inf_le_left
      have h3 : Nat.card (J z) ≤ Nat.card (H z) := Subgroup.card_le_of_le (J_le_H (z := z))
      rw [card_J h] at h3
      omega
    have hX' : CFSG.Blueprint.LieModel ↥G₁ .PSU 6 2 1 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm hX
    have hAut : Nat.card (MulAut ↥G₁) ∣ 6 * Nat.card ↥G₁ := by
      have h1 := CFSG.EvenSmallLie.UnitarySix.YamadaEnd.card_mulAut_dvd (X := ↥G₁)
      rwa [CFSG.EvenSmallLie.UnitarySix.YamadaEnd.card_outer_of_lieModel_PSU hX'] at h1
    obtain ⟨c, hcG₀, hcc, hcg⟩ :=
      exists_central_involution_not_mem_of_index_four hG₀i hG₁G₀ hG₁i hsimple hbig hC hAut
    have hcH : c ∈ centerIn (H z) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [H_eq_centralizer, mem_centralizer_singleton_iff]
        exact (hcg z).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro x _
        exact hcg x
    have hz₁c : z₁ * c ∈ centerIn (J z) := by
      rw [hZ]
      exact Subgroup.mul_mem _ (hZ ▸ hz₁) hcH
    have hz₁cG₀ : z₁ * c ∈ G₀ :=
      (Subgroup.mul_mem_iff_of_index_two hG₀i).mpr (iff_of_false hz₁G₀ hcG₀)
    have hc1 : c ≠ 1 := fun h1 => hcG₀ (h1 ▸ G₀.one_mem)
    have hz₁z₁ : z₁ * z₁ = 1 := by
      have h1 := pow_orderOf_eq_one z₁
      rwa [hz₁2, pow_two] at h1
    have hcz₁ : c = z₁ := by
      rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).mp hz₁c with h1 | h1 | h1 | h1
      · calc c = z₁ * (z₁ * c) := by rw [← mul_assoc, hz₁z₁, one_mul]
          _ = z₁ := by rw [h1, mul_one]
      · exfalso
        obtain ⟨g, hg, -, hgz⟩ := hfuse
        apply hgz
        have hgz₁ : g * z₁ = z₁ * g := mem_centralizer_singleton_iff.mp hg
        have hz₁eq : z₁ = z * c := by
          calc z₁ = z₁ * c * c := by
                calc z₁ = z₁ * (c * c) := by rw [hcc, mul_one]
                  _ = z₁ * c * c := by rw [mul_assoc]
            _ = z * c := by rw [h1]
        have h3 : g * z * c = z * g * c := by
          calc g * z * c = g * (z * c) := by rw [mul_assoc]
            _ = g * z₁ := by rw [hz₁eq]
            _ = z₁ * g := hgz₁
            _ = (z * c) * g := by rw [hz₁eq]
            _ = z * (c * g) := by rw [mul_assoc]
            _ = z * (g * c) := by rw [(hcg g).symm]
            _ = z * g * c := by rw [mul_assoc]
        have h4 : g * z = z * g := mul_right_cancel h3
        calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [h4]
          _ = z := by group
      · exfalso
        exact hc1 (by
          calc c = z₁⁻¹ * (z₁ * c) := by group
            _ = 1 := by rw [h1]; group)
      · exfalso
        apply hz₁G₀
        have h2 : z * z₁ ∈ G₀ := by
          rw [← h1]
          exact hz₁cG₀
        have h3 : z⁻¹ * (z * z₁) ∈ G₀ := G₀.mul_mem (G₀.inv_mem hzG₀) h2
        rwa [inv_mul_cancel_left] at h3
    rw [eq_top_iff]
    intro g _
    rw [mem_centralizer_singleton_iff, ← hcz₁]
    exact hcg g

end CFSG.RankThree.GF2n.Parrott
