module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Layer3
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift
import CFSG.RankThree.PartOne.S12.Sec13Base
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem le_rankThreeLayer_opp_of_coprime (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G}
    (hH : Config k H) {S : Subgroup G} (hSH : S ≤ H)
    (hS : Nat.Coprime (Nat.card S) (Nat.card (CFSG.pPrimeCore k.p ↥H)))
    (hSF : (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :
    S ≤ CFSG.Open.rankThreeLayer (UC22.Opp k.p H) ∧
      S ≤ centralizer (((CFSG.pPrimeCore k.p ↥H).map H.subtype : Subgroup G) : Set G) := by
  classical
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨hsimple, hnab, -, hFc⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI := hsimple
  set K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H with hK₀
  have hJH : layerLift k.p H ≤ H := layerLift_le k.p H
  have hmap : ((layerLift k.p H).subgroupOf H).map (QuotientGroup.mk' K₀) =
      CFSG.generalizedFitting (↥H ⧸ K₀) :=
    map_layerLift_eq k.p H
      (isPerfect_iff.mp (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1)
  have hcen : layerLift k.p H ≤ centralizer ((K₀.map H.subtype : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (h75 H hH)
  have hHK : H ≤ normalizer ((K₀.map H.subtype : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K₀)).mp
      (by
        rw [show (K₀.map H.subtype).subgroupOf H = K₀ from
          comap_map_eq_self_of_injective H.subtype_injective K₀]
        infer_instance)
  have hSJ : S ≤ layerLift k.p H := by
    refine CFSG.RankThree.PartTwo.Sec21.FF79.L14.le_of_coprime_relIndex
      (D := K₀.map H.subtype ⊔ layerLift k.p H) le_sup_right (fun d hd x hx => ?_)
      (fun s hs => ?_) ?_
    · exact (mem_normalizer_iff.mp (le_normalizer_layerLift k.p H
        (sup_le (map_subtype_le K₀) hJH hd)) x).mp hx
    · have hsL : QuotientGroup.mk' K₀ (⟨s, hSH hs⟩ : ↥H) ∈
          ((layerLift k.p H).subgroupOf H).map (QuotientGroup.mk' K₀) :=
        hmap ▸ hSF ⟨⟨s, hSH hs⟩, mem_subgroupOf.mpr hs, rfl⟩
      obtain ⟨j, hjJ, hjs⟩ := mem_map.mp hsL
      have hc : j⁻¹ * ⟨s, hSH hs⟩ ∈ K₀ := QuotientGroup.eq.mp hjs
      have hs' : s = (j : G) * ((j⁻¹ * ⟨s, hSH hs⟩ : ↥H) : G) := by simp
      rw [hs']
      exact mul_mem (mem_sup_right (mem_subgroupOf.mp hjJ)) (mem_sup_left ⟨_, hc, rfl⟩)
    · rw [CFSG.ABGTheoremB.relIndex_sup_eq_relIndex_of_le_normalizer (hJH.trans hHK)]
      refine Nat.Coprime.coprime_dvd_right (relIndex_dvd_card _ _) ?_
      rwa [card_map_of_injective H.subtype_injective]
  have hdvd : k.p ∣ Nat.card ↥(layerLift k.p H) := by
    have h1 := k.dvd_card_generalizedFitting_quotient hH
    rw [← hmap] at h1
    exact h1.trans ((card_map_dvd _ _).trans
      (dvd_of_eq (Nat.card_congr (subgroupOfEquivOfLe hJH).toEquiv)))
  have hZ : ¬ k.p ∣ Nat.card ↥(center ↥(layerLift k.p H)) := by
    intro hp
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' k.p hp
    have hzH : ((z : ↥(layerLift k.p H)) : G) ∈ H := hJH (z : ↥(layerLift k.p H)).2
    have hzc : QuotientGroup.mk' K₀ ⟨_, hzH⟩ ∈
        centralizer (CFSG.generalizedFitting (↥H ⧸ K₀) : Set (↥H ⧸ K₀)) := by
      rw [mem_centralizer_iff]
      intro y hy
      rw [← hmap] at hy
      obtain ⟨j, hjJ, rfl⟩ := mem_map.mp hy
      have hzj : (j : G) * ((z : ↥(layerLift k.p H)) : G) =
          ((z : ↥(layerLift k.p H)) : G) * j :=
        congrArg Subtype.val (mem_center_iff.mp z.2 ⟨(j : G), mem_subgroupOf.mp hjJ⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hzj)
    rw [hFc, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzc
    have h1 := K₀.orderOf_dvd_natCard hzc
    rw [orderOf_mk, orderOf_coe, orderOf_coe, hz] at h1
    exact (k.prime.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card h1
  have hJq : CFSG.IsQuasisimple ↥(layerLift k.p H) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.isQuasisimple_iff_cfsg _).mp
      (k.isComponentOf_layerLift h75 hH).2.2
  have hOH : UC22.Opp k.p H ≤ H := (closure_le H).mpr fun x hx => hx.1
  have hJO : layerLift k.p H ≤ UC22.Opp k.p H := by
    refine (CFSG.RankThree.PartOne.Sec13Base.le_closure_pElements k.prime hJq hZ hdvd).trans
      ((closure_le _).mpr fun y hy => subset_closure ⟨hJH hy.1, ?_⟩)
    rcases (Nat.dvd_prime k.prime).mp (orderOf_dvd_of_pow_eq_one hy.2) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hJc : CFSG.Open.IsComponentOf (layerLift k.p H) (UC22.Opp k.p H) :=
    ⟨hJO, CFSG.Open.IsSubnormal.step hJO
      ((normal_subgroupOf_iff_le_normalizer hJO).mpr (hOH.trans (le_normalizer_layerLift k.p H)))
      (CFSG.Open.IsSubnormal.refl _), (k.isComponentOf_layerLift h75 hH).2.2⟩
  refine ⟨hSJ.trans ?_, hSJ.trans hcen⟩
  unfold CFSG.Open.rankThreeLayer
  exact le_sSup hJc

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
