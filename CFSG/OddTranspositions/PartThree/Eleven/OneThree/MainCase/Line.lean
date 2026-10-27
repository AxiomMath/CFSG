module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Coset
import CFSG.OddTranspositions.PartFour.LineSpan
import CFSG.OddTranspositions.PartFour.LineVmem
import CFSG.OddTranspositions.PartFour.SeventeenTwo
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.OddTranspositions.PartFour.LineStabilizer

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}


namespace MainHyp

variable {hC : HypothesisC D}

private theorem commute_conj_of_mem_pCore (hC : HypothesisC D)
    {v c : Halpha D hC.alpha} (hv : (v : G) ∈ DalphaStar D hC.alpha)
    (hcD : (c : G) ∈ D) (hvc : Commute (v : G) (c : G))
    {q : Halpha D hC.alpha} (hq : q ∈ CFSG.pCore 2 (Halpha D hC.alpha)) :
    Commute ((q : G) * (v : G) * (q : G)⁻¹) (c : G) := by
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  haveI : Q.Normal := CFSG.pCore_normal
  have hvD : (v : G) ∈ D := DalphaStar_subset hC.isBlock_alpha hv
  have hv2 : v * v = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hvD)
  have hc2 : c * c = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hcD)
  have hvcH : Commute v c := by
    show v * c = c * v
    exact Subtype.ext hvc
  have hq1 : QuotientGroup.mk' Q q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
  have hvq : QuotientGroup.mk' Q (q * v * q⁻¹) = QuotientGroup.mk' Q v := by
    rw [map_mul, map_mul, map_inv, hq1, one_mul, inv_one, mul_one]
  have hv2q : (QuotientGroup.mk' Q v) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hv2, map_one]
  have hc2q : (QuotientGroup.mk' Q c) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hc2, map_one]
  have hsq : (q * v * q⁻¹ * c) ^ 2 ∈ Q := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    rw [map_pow, map_mul, hvq, (hvcH.map (QuotientGroup.mk' Q)).mul_pow, hv2q, hc2q, one_mul]
  have hqN : (q : G) ∈ Subgroup.normalizer (DalphaStar D hC.alpha) :=
    Halpha_le_normalizer hC.setup.normal q.2
  have hvqStar : ((q * v * q⁻¹ : H) : G) ∈ DalphaStar D hC.alpha := by
    simpa using (hqN (v : G)).mp hv
  have hcomm := commute_of_mul_sq_mem_pCore hC
    (DalphaStar_subset hC.isBlock_alpha hvqStar) hcD hsq
  simpa using hcomm

private theorem mem_perp_cimg_of_commute (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {q : Halpha D hC.alpha} (hq : q ∈ CFSG.pCore 2 (Halpha D hC.alpha))
    {v c : G} (hvβ : v ∈ β) (hcγ : c ∈ γ) (hvc : Commute v c) :
    cimg (q : G) β ∈ perp D γ := by
  have hv : v ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hvβ
  have hc : c ∈ DalphaStar D hC.alpha := subset_DalphaStar hγ hcγ
  have hqD := smul_mem_Dalpha_of_mem_Halpha hC q.2 hβ
  let vH : Halpha D hC.alpha := ⟨v, Subgroup.subset_closure hv⟩
  let cH : Halpha D hC.alpha := ⟨c, Subgroup.subset_closure hc⟩
  have hvH : (vH : G) ∈ DalphaStar D hC.alpha := by simpa [vH] using hv
  have hcH : (cH : G) ∈ D := by
    simpa [cH] using DalphaStar_subset hC.isBlock_alpha hc
  have hvcH : Commute (vH : G) (cH : G) := by simpa [vH, cH] using hvc
  exact mem_perp_of_commute hC hγ.1 hqD.1 hcγ ⟨v, hvβ, rfl⟩
    (commute_conj_of_mem_pCore hC (v := vH) (c := cH) hvH hcH hvcH hq).symm

private theorem mem_blockLine_cimg (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {q : Halpha D hC.alpha}
    (hq : q ∈ CFSG.pCore 2 (Halpha D hC.alpha)) :
    cimg (q : G) β ∈ blockLine D hC.alpha β := by
  refine mem_blockLine_iff.mpr ⟨(smul_mem_Dalpha_of_mem_Halpha hC q.2 hβ).1, ?_⟩
  rintro γ ⟨hγα, hγβ⟩
  by_cases hγα' : γ = hC.alpha
  · rw [hγα']
    exact mem_perp_iff.mpr (Or.inl (smul_mem_Dalpha_of_mem_Halpha hC q.2 hβ))
  · have hγDα : γ ∈ Dalpha D hC.alpha := (mem_perp_iff.mp hγα).resolve_right hγα'
    obtain ⟨v, hvβ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
    by_cases hγβ' : γ = β
    · rw [hγβ']
      exact mem_perp_cimg_of_commute hC hβ hβ hq hvβ hvβ (Commute.refl v)
    · have hγDβ : γ ∈ Dalpha D β := (mem_perp_iff.mp hγβ).resolve_right hγβ'
      obtain ⟨c, hcγ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγDα.1
      exact mem_perp_cimg_of_commute hC hβ hγDα hq hvβ hcγ
        ((mem_Dalpha_iff.mp hγDβ).2.2.2 v hvβ c hcγ)

private theorem exists_cimg_eq_of_mul_mem_pCore (h : MainHyp hC) {β δ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hδ : δ ∈ Dalpha D hC.alpha)
    (hδβ : δ ∈ Dalpha D β) {v w : Halpha D hC.alpha}
    (hvβ : (v : G) ∈ β) (hwδ : (w : G) ∈ δ)
    (hwv : w * v ∈ CFSG.pCore 2 (Halpha D hC.alpha)) :
    ∃ q ∈ CFSG.pCore 2 (Halpha D hC.alpha), cimg (q : G) β = δ := by
  have hvD : (v : G) ∈ D := hβ.2.1 hvβ
  have hv2 : (v : G) * (v : G) = 1 := hC.setup.oddT.mul_self_eq_one hvD
  have hwq : (w : G) = ((w * v : Halpha D hC.alpha) : G) * (v : G) := by
    rw [Subgroup.coe_mul, mul_assoc, hv2, mul_one]
  obtain ⟨r, hr, hrv⟩ := h.exists_pCore_conj_eq (x := (v : G)) (w := (w : G))
    (subset_DalphaStar hβ hvβ) (hδ.2.1 hwδ) (q := w * v) hwv hwq
  refine ⟨r, hr, ?_⟩
  have hmeet : (δ ∩ cimg (r : G) β).Nonempty :=
    ⟨(w : G), hwδ, ⟨(v : G), hvβ, hrv⟩⟩
  exact (eq_of_mem_of_mem_blockClass hC.isBlock_alpha hδ.1
    (smul_mem_Dalpha_of_mem_Halpha hC r.2 hβ).1 hmeet).symm

private theorem false_of_mul_not_mem_pCore (h : MainHyp hC) {β δ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hδ : δ ∈ Dalpha D hC.alpha)
    (hδline : δ ∈ blockLine D hC.alpha β) (hδβ : δ ≠ β)
    (hδDβ : δ ∈ Dalpha D β) {v w : Halpha D hC.alpha}
    (hvβ : (v : G) ∈ β) (hwδ : (w : G) ∈ δ)
    (hwv : w * v ∉ CFSG.pCore 2 (Halpha D hC.alpha)) : False := by
  have hvD : (v : G) ∈ D := hβ.2.1 hvβ
  have hwD : (w : G) ∈ D := hδ.2.1 hwδ
  have hwvG : Commute (w : G) (v : G) :=
    ((mem_Dalpha_iff.mp hδDβ).2.2.2 (v : G) hvβ (w : G) hwδ).symm
  obtain ⟨k, hk, hnc, hbβ⟩ := h.exists_conj_not_commute hβ hvβ
  set b : G := (k : G) * (v : G) * (k : G)⁻¹ with hbdef
  have hnc' : ¬ Commute (v : G) b := by simpa [hbdef] using hnc
  have hwb : Commute (w : G) b := by
    simpa [hbdef] using
      commute_conj_of_mul_not_mem_pCore hC hwD hvD hwvG hwv hk
  have hbStar : b ∈ DalphaStar D hC.alpha := by
    have hqN : (k : G) ∈ Subgroup.normalizer (DalphaStar D hC.alpha) :=
      Halpha_le_normalizer hC.setup.normal k.2
    have hvStar : (v : G) ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hvβ
    simpa [hbdef] using (hqN (v : G)).mp hvStar
  obtain ⟨β', hβ'Dα, hbβ'⟩ := mem_DalphaStar_iff.mp hbStar
  have hβ'ne : β' ≠ β := fun h => hbβ (h ▸ hbβ')
  have hperpδ : β' ∈ perp D δ :=
    mem_perp_of_commute hC hδ.1 hβ'Dα.1 hwδ hbβ' hwb
  have hperpα : β' ∈ perp D hC.alpha := mem_perp_iff.mpr (Or.inl hβ'Dα)
  have hline : blockLine D hC.alpha δ = blockLine D hC.alpha β :=
    blockLine_eq_of_mem hC hβ hδ hδline
  have hβline : β ∈ blockLine D hC.alpha δ := by
    rw [hline]
    exact right_mem_blockLine hβ.1 hβ.2.1
  have hβperp : β ∈ perp D β' := hβline.2 β' ⟨hperpα, hperpδ⟩
  have hβDβ' : β ∈ Dalpha D β' := hβperp.resolve_right (Ne.symm hβ'ne)
  exact hnc' (((mem_Dalpha_iff.mp hβDβ').2.2.2 b hbβ' (v : G) hvβ).symm)

theorem blockLine_eq (h : MainHyp hC) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    blockLine D hC.alpha β = insert hC.alpha ((fun q => cimg q β) ''
      ((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Set G)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro δ hδ
    by_cases hδα : δ = hC.alpha
    · exact Or.inl hδα
    have hδDα : δ ∈ Dalpha D hC.alpha :=
      mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hδ hδα
    by_cases hδβ : δ = β
    · refine Or.inr ⟨1, ?_, ?_⟩
      · simpa using Subgroup.mem_map_of_mem (Halpha D hC.alpha).subtype
          (Subgroup.one_mem (CFSG.pCore 2 (Halpha D hC.alpha)))
      · change cimg 1 β = δ
        rw [cimg_one]
        exact hδβ.symm
    · have hδDβ : δ ∈ Dalpha D β := by
        have hperp : δ ∈ perp D β :=
          mem_perp_of_mem_blockLine hC.isBlock_alpha.subset hβ
            (right_mem_blockLine hβ.1 hβ.2.1) hδ
        exact hperp.resolve_right hδβ
      obtain ⟨v, hvβ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
      obtain ⟨w, hwδ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hδDα.1
      let vH : Halpha D hC.alpha :=
        ⟨v, Subgroup.subset_closure (subset_DalphaStar hβ hvβ)⟩
      let wH : Halpha D hC.alpha :=
        ⟨w, Subgroup.subset_closure (subset_DalphaStar hδDα hwδ)⟩
      by_cases hwv : wH * vH ∈ CFSG.pCore 2 (Halpha D hC.alpha)
      · obtain ⟨q, hq, hqeq⟩ :=
          exists_cimg_eq_of_mul_mem_pCore h hβ hδDα hδDβ hvβ hwδ hwv
        exact Or.inr ⟨q, Subgroup.mem_map_of_mem _ hq, hqeq⟩
      · exact absurd
          (false_of_mul_not_mem_pCore h hβ hδDα hδ hδβ hδDβ hvβ hwδ hwv) (by simp)
  · intro δ hδ
    rcases hδ with rfl | hδ
    · exact left_mem_blockLine hC.isBlock_alpha.subset
    obtain ⟨g, hg, hgδ⟩ := hδ
    obtain ⟨q, hq, rfl⟩ := hg
    rw [← hgδ]
    exact mem_blockLine_cimg hC hβ hq

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
