module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointInvariantCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowGrowth

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G] [Finite G]

theorem normal_kernel_sylow_enlargement
    (R Q : Subgroup G) [R.Normal] (p : ℕ) (hp : p.Prime) (hQ : IsPGroup p Q) :
    ∃ T : Subgroup G, IsPGroup p T ∧ Q ≤ T ∧ T ≤ Q ⊔ R ∧ T ⊔ R = Q ⊔ R ∧
      (∃ S : Sylow p R, (S : Subgroup R).map R.subtype = T ⊓ R) := by
  let : Fact p.Prime := ⟨hp⟩
  let B := Q ⊔ R
  obtain ⟨P, hQP⟩ := hQ.comap_subtype.exists_le_sylow (G := B)
  let T := (P : Subgroup B).map B.subtype
  have hQT : Q ≤ T := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (le_sup_left : Q ≤ B)]
    exact Subgroup.map_mono hQP
  have hTB : T ≤ B := Subgroup.map_subtype_le _
  have hjoin : T ⊔ R = B :=
    le_antisymm (sup_le hTB le_sup_right) (sup_le (hQT.trans le_sup_left) le_sup_right)
  have hRimage : (R.subgroupOf B).map B.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hS := normal_subgroup_image_sylow_intersection p hp B (R.subgroupOf B) P
  refine ⟨T, P.isPGroup'.map B.subtype, hQT, hTB, hjoin, ?_⟩
  rw [hRimage] at hS
  exact hS

omit [Finite G] in
theorem whole_fixed_set_eq_of_normal_join
    (H R Q T : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hQT : Q ≤ T) (hTjoin : T ≤ Q ⊔ R)
    (hRfix : ∀ omega ∈ Delta, ∀ r ∈ R, pointRightCosetMul H omega r = omega) :
    Delta ∩ pointFixedSet H T = Delta ∩ pointFixedSet H Q := by
  ext omega
  constructor
  · rintro ⟨hDelta, hT⟩
    exact ⟨hDelta, pointFixedSet_antitone hQT hT⟩
  · rintro ⟨hDelta, hQ⟩
    refine ⟨hDelta, (mem_pointFixedSet_iff H T omega).mpr ?_⟩
    have hQstab : Q ≤ rightCosetStabilizer H omega :=
      (mem_pointFixedSet_iff H Q omega).mp hQ
    have hRstab : R ≤ rightCosetStabilizer H omega := by
      intro r hr
      exact (mem_point_right_stabilizer_iff H omega r).mpr (hRfix omega hDelta r hr)
    exact hTjoin.trans (sup_le hQstab hRstab)

omit [Finite G] in
theorem enlarged_centralizer_eq_supplied_sylow
    (B X T : Subgroup G) (p : ℕ)
    (Q : Sylow p (B ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    (hT : IsPGroup p T) (hTB : T ≤ B)
    (hQT : (Q : Subgroup (B ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)).map
      (B ⊓ Subgroup.centralizer (X : Set G)).subtype ≤ T) :
    T ⊓ Subgroup.centralizer (X : Set G) =
      (Q : Subgroup (B ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)).map
        (B ⊓ Subgroup.centralizer (X : Set G)).subtype := by
  have hh := noncentralSylow_containing_pgroup_intersection p _ Q T hT hQT
  have heq : T ⊓ (B ⊓ Subgroup.centralizer (X : Set G)) =
      T ⊓ Subgroup.centralizer (X : Set G) := by
    ext g
    exact ⟨fun hg => ⟨hg.1, hg.2.2⟩, fun hg => ⟨hg.1, hTB hg.1, hg.2⟩⟩
  rwa [heq] at hh

omit [Finite G] in
theorem enlarged_centralizer_normalizer
    (T X : Subgroup G) {s : G}
    (hsT : s ∈ Subgroup.normalizer (T : Set G))
    (hsX : s ∈ Subgroup.normalizer (X : Set G)) :
    s ∈ Subgroup.normalizer (T ⊓ Subgroup.centralizer (X : Set G) : Set G) := by
  have hXC : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (X : Set G))).mp inferInstance
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hsT, hXC hsX⟩

end CFSG.ShultStronglyClosedTI.CentralizerSylow
