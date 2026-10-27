module

public import CFSG.RankThree.GF2n.Parrott.Section2Theorem1EqualityBranch
import CFSG.RankThree.GF2n.Parrott.ZFusionControlHyp
import CFSG.RankThree.GF2n.Parrott.DerivedInterJEqBranch
import CFSG.RankThree.GF2n.Parrott.Section2Lemma11aEqualityBranch
import CFSG.RankThree.GF2n.Parrott.Section2Lemma11bEqualityBranch
import CFSG.RankThree.GF2n.Parrott.SigmaStarEquality
import CFSG.RankThree.GF2n.Parrott.Lemma13EqualityBranch
import CFSG.RankThree.GF2n.Parrott.Lemma14K
import CFSG.RankThree.GF2n.Parrott.ConjZPH
import CFSG.RankThree.GF2n.Parrott.Lemma15EqualityE
import CFSG.RankThree.GF2n.Parrott.Lemma16EqualityClasses
import CFSG.RankThree.GF2n.Parrott.Lemma16EqualityFusion

public section

namespace CFSG.RankThree.GF2n.Parrott

theorem parrott_theorem1_equalityBranch_holds :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤ :=
  parrott_theorem1_equalityBranch
    (fun _ _ _ _ h => normalizerControlsCenterJFusion_of_parrottHyp h)
    (fun _ _ _ _ h _ D hbr => derived_inter_J_le_J1sub_of_equalityBranch D h hbr)
    (fun _ _ _ _ h _ D hbr _ hjZ hj1 _ hCK hKS =>
      zpowers_le_commutator_derived_of_equalityBranch D h hbr hjZ hj1 hCK hKS)
    (fun _ _ _ _ h _ D hbr _ hj2 hjZ hj1 =>
      exists_lemma11b_inputs_of_equalityBranch h D hbr hj2 hjZ hj1)
    (fun _ _ _ _ h _ D _ hσ₂ hq₂ hcomm hEq hJ _ hσ =>
      star_zpowers_sigma1Nine_mul_inv_of_equalityBranch D h hσ₂ hq₂ hcomm hEq hJ hσ)
    (fun _ _ _ _ h _ D _ hσ₂ hq₂ hcomm _ hσ =>
      normalizer_zpowers_sigma1Nine_mul_inv_le_mul_centralizer D h hσ₂ hq₂ hcomm hσ)
    (fun _ _ _ _ h _ D _ hσ₂ hq₂ hcomm hEq hJ _ hσ hstar hNσ =>
      no_conj_z_eq_of_mem_tJ_equalityBranch D h hσ₂ hq₂ hcomm hEq hJ hσ hstar hNσ)
    (fun _ _ _ _ h _ D _ hσ₂ hq₂ hcomm hEq hJ =>
      no_conj_z_eq_of_mem_tuJ D h hσ₂ hq₂ hcomm hEq hJ)
    (fun _ _ _ _ h _ D hJ ht htu => conj_z_mem_P_H_eq_of_cosets D h hJ ht htu)
    (fun _ _ _ _ h _ D hJ ht htu => conj_z_mem_derived_eq_of_cosets D h hJ ht htu)
    (fun _ _ _ _ h _ D hbr => by
      obtain ⟨_, hσ₂, hq₂, hcomm, hEq⟩ := exists_commuting_lift_of_equalityBranch D h hbr
      exact exists_order_five_subgroup_extraspecial_conj_mem_uvJ D h hσ₂ hq₂ hcomm hEq)
    (fun _ _ _ _ h _ D hbr => by
      obtain ⟨_, hσ₂, hq₂, hcomm, hEq⟩ := exists_commuting_lift_of_equalityBranch D h hbr
      exact exists_two_J_classes_of_mem_uvtJ D h hσ₂ hq₂ hcomm hEq)
    (fun _ _ _ _ h _ D _ hσ₂ hq₂ hcomm hEq _ hσ _ hxc hx2 hxσ hxE _ _ hX hK =>
      exists_fusion_subgroup_of_mem_uvtJ D h hσ₂ hq₂ hcomm hEq hσ hxc hx2 hxσ hxE hX hK)

end CFSG.RankThree.GF2n.Parrott
