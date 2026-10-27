module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowGrowth

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u

variable {G : Type u} [Group G]

theorem normalizer_fixes_second_point
    (H Q F : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ f ∈ F, ∀ omega ∈ Delta, pointRightCosetMul H omega f ∈ Delta)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hbetaDelta : beta ∈ Delta) (hbetaQ : beta ∈ pointFixedSet H Q)
    (hfixed : Delta ∩ pointFixedSet H Q = {rightCosetMk H 1, beta})
    (n : G) (hnF : n ∈ F) (hnH : n ∈ H)
    (hnQ : n ∈ Subgroup.normalizer (Q : Set G)) :
    pointRightCosetMul H beta n = beta := by
  have hmem : pointRightCosetMul H beta n ∈ Delta ∩ pointFixedSet H Q :=
    ⟨hstable n hnF beta hbetaDelta, normalizer_preserves_pointFixedSet hnQ hbetaQ⟩
  rw [hfixed] at hmem
  rcases hmem with hbase | hsecond
  · have heq : pointRightCosetMul H beta n =
        pointRightCosetMul H (rightCosetMk H 1) n :=
      hbase.trans ((point_right_base_fixed_iff H n).mpr hnH).symm
    have hback := congrArg (fun omega => pointRightCosetMul H omega n⁻¹) heq
    exact False.elim (hbeta (by
      simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one] using hback))
  · exact hsecond

theorem two_point_centralizer_sylow_promotion
    [Finite G] (H X F : Subgroup G)
    (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ f ∈ F, ∀ omega ∈ Delta, pointRightCosetMul H omega f ∈ Delta)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hbetaDelta : beta ∈ Delta)
    (p : ℕ) (hp : p.Prime)
    (Q : Sylow p (pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    (hQF : (Q : Subgroup (pairPointStabilizer H beta ⊓
      Subgroup.centralizer (X : Set G) : Subgroup G)).map
        (pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G)).subtype ≤ F)
    (hfixed : Delta ∩ pointFixedSet H
      ((Q : Subgroup (pairPointStabilizer H beta ⊓
        Subgroup.centralizer (X : Set G) : Subgroup G)).map
          (pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G)).subtype) =
      {rightCosetMk H 1, beta}) :
    ∃ P : Sylow p ((H ⊓ F) ⊓ Subgroup.centralizer (X : Set G) : Subgroup G),
      (P : Subgroup ((H ⊓ F) ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)).map
        ((H ⊓ F) ⊓ Subgroup.centralizer (X : Set G)).subtype =
      (Q : Subgroup (pairPointStabilizer H beta ⊓
        Subgroup.centralizer (X : Set G) : Subgroup G)).map
          (pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G)).subtype := by
  let B := pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G)
  let D := (H ⊓ F) ⊓ Subgroup.centralizer (X : Set G)
  let QG := (Q : Subgroup B).map B.subtype
  have hQB : QG ≤ B := Subgroup.map_subtype_le _
  have hQH : QG ≤ H := (hQB.trans inf_le_left).trans (by
    rw [pairPointStabilizer, rightCosetStabilizer_base]
    exact inf_le_left)
  have hQD : QG ≤ D := le_inf (le_inf hQH hQF) (hQB.trans inf_le_right)
  have hbetaQ : beta ∈ pointFixedSet H QG :=
    (mem_pointFixedSet_iff H QG beta).mpr
      ((hQB.trans inf_le_left).trans inf_le_right)
  let QD := QG.subgroupOf D
  have hQDmap : QD.map D.subtype = QG := Subgroup.map_subgroupOf_eq_of_le hQD
  have hQp : IsPGroup p QG := Q.isPGroup'.map B.subtype
  let P : Sylow p D := ⟨QD, hQp.comap_subtype, by
    intro S hSp hQDS
    let SG := S.map D.subtype
    have hSGp : IsPGroup p SG := hSp.map D.subtype
    have hQSG : QG ≤ SG := by
      rw [← hQDmap]
      exact Subgroup.map_mono hQDS
    have hSGD : SG ≤ D := Subgroup.map_subtype_le _
    have hSGQ : SG ≤ QG := by
      by_contra hnot
      have hlt : QG < SG := lt_of_le_not_ge hQSG hnot
      obtain ⟨n, hn, hnnot⟩ := IsConcreteLE.exists_of_lt
        (pSubgroup_lt_normalizer_intersection p hp QG SG hSGp hlt)
      have hnD := hSGD hn.1
      have hnbeta := normalizer_fixes_second_point H QG F Delta hstable beta hbeta
        hbetaDelta hbetaQ hfixed n hnD.1.2 hnD.1.1 hn.2
      have hnB : n ∈ B := ⟨by
        change n ∈ rightCosetStabilizer H (rightCosetMk H 1) ⊓
          rightCosetStabilizer H beta
        exact ⟨by simpa only [rightCosetStabilizer_base] using hnD.1.1,
          (mem_point_right_stabilizer_iff H beta n).mpr hnbeta⟩, hnD.2⟩
      have hintersection := noncentralSylow_containing_pgroup_intersection p B Q SG hSGp hQSG
      have hnQ : n ∈ QG := by
        change n ∈ (Q : Subgroup B).map B.subtype
        rw [← hintersection]
        exact ⟨hn.1, hnB⟩
      exact hnnot hnQ
    apply Subgroup.map_injective D.subtype_injective
    exact (le_antisymm hSGQ hQSG).trans hQDmap.symm⟩
  exact ⟨P, hQDmap⟩

end CFSG.ShultStronglyClosedTI.CentralizerSylow
