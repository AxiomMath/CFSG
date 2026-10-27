module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.RankThree.PartTwo.Census.Alternating
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import Certificates.Certificate8064
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeTransport
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Blueprint

theorem fs81Hl_not_solvable_of_commutator_top {L : Type*} [Group L] [Nontrivial L]
    (h : commutator L = ⊤) : ¬ Group.IsSolvable L := by
  intro hsol
  letI : Group.IsPerfect L := Group.isPerfect_def.mpr h
  exact Group.IsPerfect.not_isSolvable L hsol

theorem fs81Hl_sylow2In_sylow {G : Type} [Group G] [Finite G] {Y S : Subgroup G} {t : G}
    (hSyl : IsSylow2In S Y) (htS : t ∈ S) (hconj : ∀ g : G, g * t * g⁻¹ ∈ Y → g ∈ Y) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = S := by
  classical
  obtain ⟨P, hSP⟩ := hSyl.2.1.exists_le_sylow
  have hPS : (P : Subgroup G) = S := by
    by_contra hne
    have hlt : S < (P : Subgroup G) := lt_of_le_of_ne hSP (Ne.symm hne)
    have hgrowth :=
      CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime.pSubgroup_lt_normalizer_intersection
        2 Nat.prime_two S (P : Subgroup G) P.isPGroup' hlt
    obtain ⟨x, hx, hxS⟩ := Set.exists_of_ssubset hgrowth
    have hxP : x ∈ (P : Subgroup G) := (Subgroup.mem_inf.mp hx).1
    have hxN : x ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxtS : x * t * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxN t).mp htS
    have hxY : x ∈ Y := hconj x (hSyl.1 hxtS)
    have h2 : IsPGroup 2 (S ⊔ Subgroup.zpowers x : Subgroup G) :=
      P.isPGroup'.to_le (sup_le hSP (Subgroup.zpowers_le.mpr hxP))
    have hEq : S ⊔ Subgroup.zpowers x = S :=
      hSyl.2.2 (S ⊔ Subgroup.zpowers x) (sup_le hSyl.1 (Subgroup.zpowers_le.mpr hxY))
        h2 le_sup_left
    exact hxS (by rw [← hEq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  exact ⟨P, hPS⟩

theorem fs81Hl_lieModel_of_marked {R : Type} [Group R] {lab : LargeEvenLabel} {m : ℕ}
    (hcase : (m = 7 ∧ lab.tag = .E7) ∨ (m = 8 ∧ lab.tag = .E8))
    (hrank : lab.rank = 0) (hn : lab.n = 1) (hm : MarkedModel lab R) :
    LieModel R .E7 0 2 1 ∨ LieModel R .E8 0 2 1 := by
  rcases hcase with ⟨-, htag⟩ | ⟨-, htag⟩
  · left
    simpa only [MarkedModel, markTag, markRank, markChar, markDeg, htag, hrank, hn] using hm
  · right
    simpa only [MarkedModel, markTag, markRank, markChar, markDeg, htag, hrank, hn] using hm

theorem fs81Hl_card_gt_2520
    {G : Type} [Group G] [Finite G] {m : ℕ} {Y : Subgroup G} (hEm : IsEm m Y) :
    2520 < Nat.card Y := by
  obtain ⟨-, lab, -, R, hRgrp, I, F, θ, -, -, hP⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists
      (CFSG.StandardType.Canonical.largeEvenMarking_markedModel hEm)
  have hLie := fs81Hl_lieModel_of_marked hP.1.1 hP.1.2.1 hP.1.2.2 hP.2
  have hcardR : Nat.card R = ordE7 2 ∨ Nat.card R = ordE8 2 := by
    rcases hLie with h | h
    · exact Or.inl (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_E7 h)
    · exact Or.inr (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_E8 h)
  have hquot : Nat.card (Y ⧸ Subgroup.center Y) = Nat.card R := Nat.card_congr θ.toEquiv
  have hYcard : Nat.card Y =
      Nat.card (Y ⧸ Subgroup.center Y) * Nat.card ↥(Subgroup.center Y) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
  have hle : Nat.card R ≤ Nat.card Y := by
    rw [hYcard, hquot]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  rcases hcardR with h | h
  · rw [h] at hle
    have : 2520 < ordE7 2 := by norm_num [CFSG.Open.ordE7]
    exact lt_of_lt_of_le this hle
  · rw [h] at hle
    have : 2520 < ordE8 2 := by norm_num [CFSG.Open.ordE8]
    exact lt_of_lt_of_le this hle

end CFSG.StandardType.FrameRoute.FS81
