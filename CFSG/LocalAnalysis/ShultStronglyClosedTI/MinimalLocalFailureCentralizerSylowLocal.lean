module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityStrongEmbedding
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylowOddCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylowPointClass
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylowRecognizedAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylowTwoPoint
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityAlgebra

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ShultStronglyClosedTI.TripleSylowMaximality

universe u

variable {G : Type u} [Group G] [Finite G]

theorem local_centralizer_sylow_involution_normalizer
    (H X F : Subgroup G) (hFX : F ≤ Subgroup.normalizer (X : Set G))
    (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ f ∈ F, ∀ omega ∈ Delta, pointRightCosetMul H omega f ∈ Delta)
    (halpha : rightCosetMk H 1 ∈ Delta)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hbetaDelta : beta ∈ Delta)
    (hrank : TwoRankAtLeastTwo F) (hR1 : R1Full F)
    (hA : fusionStronglyEmbedded (H.subgroupOf F))
    (htrans : letI := pointInvariantSetInverseRightAction H F Delta hstable
      MulAction.IsPretransitive F Delta)
    (z : G) (hzH : z ∈ H) (hzF : z ∈ F) (hz : orderOf z = 2)
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({z} : Set G))
    (hRfix : ∀ omega ∈ Delta, ∀ r ∈ (CFSG.oddCore F).map F.subtype,
      pointRightCosetMul H omega r = omega)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (Q : Sylow p (pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    (hQF : (Q : Subgroup (pairPointStabilizer H beta ⊓
      Subgroup.centralizer (X : Set G) : Subgroup G)).map
        (pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G)).subtype ≤ F) :
    ∃ s ∈ conjugacyWithin H z,
      s ∈ Subgroup.normalizer (X : Set G) ∧
      s ∈ Subgroup.normalizer
        (((Q : Subgroup (pairPointStabilizer H beta ⊓
          Subgroup.centralizer (X : Set G) : Subgroup G)).map
            (pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G)).subtype :
              Subgroup G) : Set G) ∧
      s ∈ Subgroup.normalizer
        ((X ⊔ (Q : Subgroup (pairPointStabilizer H beta ⊓
          Subgroup.centralizer (X : Set G) : Subgroup G)).map
            (pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G)).subtype :
              Subgroup G) : Set G) := by
  classical
  let B := pairPointStabilizer H beta
  let C := B ⊓ Subgroup.centralizer (X : Set G)
  let QG := (Q : Subgroup C).map C.subtype
  let A := H ⊓ F
  have hQB : QG ≤ B := (Subgroup.map_subtype_le _).trans inf_le_left
  have hQH : QG ≤ H := hQB.trans (by
    change rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta ≤ H
    rw [rightCosetStabilizer_base]
    exact inf_le_left)
  have hbaseQ : rightCosetMk H 1 ∈ pointFixedSet H QG :=
    (mem_pointFixedSet_iff H QG _).mpr (by
      simpa only [rightCosetStabilizer_base] using hQH)
  have hbetaQ : beta ∈ pointFixedSet H QG :=
    (mem_pointFixedSet_iff H QG beta).mpr (hQB.trans inf_le_right)
  have hclass : ∀ v ∈ A, orderOf v = 2 → v ∈ conjugacyWithin A z :=
    local_point_involution_class_ambient H F
      (native_strong_embedding_of_order_conditions hA) z hzH hzF hz
  have hzA : z ∈ A := ⟨hzH, hzF⟩
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := inf_le_right.trans hFX
  have finish (s : G) (hsclass : s ∈ conjugacyWithin A z)
      (hsQ : s ∈ Subgroup.normalizer (QG : Set G)) :
      ∃ s ∈ conjugacyWithin H z,
        s ∈ Subgroup.normalizer (X : Set G) ∧
        s ∈ Subgroup.normalizer (QG : Set G) ∧
        s ∈ Subgroup.normalizer ((X ⊔ QG : Subgroup G) : Set G) := by
    obtain ⟨a, ha⟩ := hsclass
    have hsA : s ∈ A := by
      rw [← ha]
      exact A.mul_mem (A.mul_mem (A.inv_mem a.property) hzA) a.property
    have hsX : s ∈ Subgroup.normalizer (X : Set G) := hAX hsA
    refine ⟨s, ⟨⟨a.val, a.property.1⟩, ha⟩, hsX, hsQ, ?_⟩
    exact Subgroup.inf_normalizer_le_normalizer_sup X QG ⟨hsX, hsQ⟩
  by_cases htwo : Delta ∩ pointFixedSet H QG = {rightCosetMk H 1, beta}
  · obtain ⟨P, hP⟩ := two_point_centralizer_sylow_promotion
      H X F Delta hstable beta hbeta hbetaDelta p hp Q hQF htwo
    obtain ⟨s, hsclass, hsP⟩ := point_class_centralizer_sylow_normalizer
      A X hAX z hzA hz hclass hnoncentral p hp P
    have hsQ : s ∈ Subgroup.normalizer (QG : Set G) := by
      rwa [hP] at hsP
    exact finish s hsclass hsQ
  · let := pointInvariantSetInverseRightAction H F Delta hstable
    let QF := QG.subgroupOf F
    have hQp : IsPGroup p QG := Q.isPGroup'.map C.subtype
    have hQFp : IsPGroup p QF := hQp.comap_subtype
    have hQimage : QF.map F.subtype = QG := Subgroup.map_subgroupOf_eq_of_le hQF
    obtain ⟨T, hTp, hQT, hTjoin, _hjoin, hintersection⟩ :=
      normal_kernel_sylow_enlargement (CFSG.oddCore F) QF p hp hQFp
    let TG := T.map F.subtype
    let R := (CFSG.oddCore F).map F.subtype
    have hQTG : QG ≤ TG := by
      rw [← hQimage]
      exact Subgroup.map_mono hQT
    have hTGjoin : TG ≤ QG ⊔ R := by
      have hh := Subgroup.map_mono (f := F.subtype) hTjoin
      rwa [Subgroup.map_sup, hQimage] at hh
    have hfixed : Delta ∩ pointFixedSet H TG = Delta ∩ pointFixedSet H QG :=
      whole_fixed_set_eq_of_normal_join H R QG TG Delta hQTG hTGjoin hRfix
    have hbaseT : rightCosetMk H 1 ∈ pointFixedSet H TG := by
      have hh : rightCosetMk H 1 ∈ Delta ∩ pointFixedSet H QG := ⟨halpha, hbaseQ⟩
      rw [← hfixed] at hh
      exact hh.2
    have hbetaT : beta ∈ pointFixedSet H TG := by
      have hh : beta ∈ Delta ∩ pointFixedSet H QG := ⟨hbetaDelta, hbetaQ⟩
      rw [← hfixed] at hh
      exact hh.2
    have hTG_B : TG ≤ B := le_inf
      ((mem_pointFixedSet_iff H TG _).mp hbaseT)
      ((mem_pointFixedSet_iff H TG _).mp hbetaT)
    have hpair : ({rightCosetMk H 1, beta} : Set (pointRightCosetSpace H)) ⊆
        Delta ∩ pointFixedSet H QG := by
      intro omega homega
      rcases homega with rfl | rfl
      · exact ⟨halpha, hbaseQ⟩
      · exact ⟨hbetaDelta, hbetaQ⟩
    have hnotSubset : ¬ Delta ∩ pointFixedSet H QG ⊆ {rightCosetMk H 1, beta} :=
      fun hh => htwo (Set.Subset.antisymm hh hpair)
    obtain ⟨gamma, hgamma, hgammaPair⟩ := Set.not_subset.mp hnotSubset
    have hgammaBase : gamma ≠ rightCosetMk H 1 := by
      intro hh
      exact hgammaPair (hh ▸ Set.mem_insert _ _)
    have hgammaBeta : gamma ≠ beta := by
      intro hh
      exact hgammaPair (hh ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hgammaT : gamma ∈ pointFixedSet H TG := by
      rw [← hfixed] at hgamma
      exact hgamma.2
    let alpha : Delta := ⟨rightCosetMk H 1, halpha⟩
    let betaD : Delta := ⟨beta, hbetaDelta⟩
    let gammaD : Delta := ⟨gamma, hgamma.1⟩
    have hTstab (omega : Delta) (hfix : omega.val ∈ pointFixedSet H TG) :
        T ≤ MulAction.stabilizer F omega := by
      intro t ht
      apply MulAction.mem_stabilizer_iff.mpr
      apply Subtype.ext
      exact hfix t.val⁻¹ (Subgroup.mem_map_of_mem F.subtype (T.inv_mem ht))
    have hthree : 3 ≤ Nat.card {omega : Delta //
        omega ∈ fixedPointsOfSubgroup F Delta T} := by
      exact three_le_fixed_card T (hTstab alpha hbaseT) (hTstab betaD hbetaT)
        (hTstab gammaD hgammaT)
        (fun hh => hbeta (congrArg Subtype.val hh).symm)
        (fun hh => hgammaBase (congrArg Subtype.val hh).symm)
        (fun hh => hgammaBeta (congrArg Subtype.val hh).symm)
    have hstabilizer : MulAction.stabilizer F alpha = H.subgroupOf F := by
      rw [original_restricted_stabilizer H F Delta hstable alpha, rightCosetStabilizer_base]
    let zF : F := ⟨z, hzF⟩
    have hzalpha : zF • alpha = alpha := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [hstabilizer]
      exact hzH
    have hzForder : orderOf zF = 2 := (Subgroup.orderOf_coe zF).symm.trans hz
    obtain ⟨s, hsclass, hsT⟩ := recognized_action_three_point_normalizer
      hrank hR1 htrans alpha (hstabilizer.symm ▸ hA) zF hzalpha hzForder
      p hp hpodd T hTp (hTstab alpha hbaseT) hthree hintersection
    obtain ⟨a, ha⟩ := hsclass
    have haH : (a.val : G) ∈ H := by
      exact hstabilizer.le a.property
    have hsambient : (s : G) ∈ conjugacyWithin A z :=
      ⟨⟨a.val.val, haH, a.val.property⟩, congrArg Subtype.val ha⟩
    have hsTG : (s : G) ∈ Subgroup.normalizer (TG : Set G) :=
      (normalizer_in_subgroup_iff_ambient_image F T s).mp hsT
    have hsX : (s : G) ∈ Subgroup.normalizer (X : Set G) := hFX s.property
    have hcentralizer : TG ⊓ Subgroup.centralizer (X : Set G) = QG :=
      enlarged_centralizer_eq_supplied_sylow B X TG p Q
        (hTp.map F.subtype) hTG_B hQTG
    have hsQ : (s : G) ∈ Subgroup.normalizer (QG : Set G) := by
      rw [← hcentralizer]
      exact enlarged_centralizer_normalizer TG X hsTG hsX
    exact finish s.val hsambient hsQ

end CFSG.ShultStronglyClosedTI.CentralizerSylow
