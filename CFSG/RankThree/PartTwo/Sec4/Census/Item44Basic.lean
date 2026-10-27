module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG

variable {G : Type*} [Group G]

theorem le_of_isSolvable_of_normal [Group.IsPerfect G] {K : Subgroup G} [K.Normal]
    [IsSimpleGroup (G ⧸ K)] {N : Subgroup G} (hN : N.Normal) (hsol : Group.IsSolvable N) :
    N ≤ K := by
  have hM : (N.map (QuotientGroup.mk' K)).Normal := hN.map _ (QuotientGroup.mk'_surjective K)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' K)) with h | h
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · exfalso
    have h1 : Group.IsSolvable (N.map (QuotientGroup.mk' K)) :=
      Group.isSolvable_of_surjective ((QuotientGroup.mk' K).subgroupMap_surjective N)
    have h2 : Group.IsSolvable (⊤ : Subgroup (G ⧸ K)) := h ▸ h1
    have h3 : Group.IsSolvable (G ⧸ K) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := G ⧸ K)).toMonoidHom)
        (Subgroup.topEquiv (G := G ⧸ K)).surjective
    exact Group.IsPerfect.not_isSolvable (G ⧸ K) h3

theorem pCore_le [Group.IsPerfect G] [Finite G] {K : Subgroup G} [K.Normal]
    [IsSimpleGroup (G ⧸ K)] (p : ℕ) [Fact p.Prime] : pCore p G ≤ K :=
  haveI : Group.IsNilpotent (pCore p G) := pCore_isPGroup.isNilpotent
  le_of_isSolvable_of_normal pCore_normal inferInstance

theorem eq_top_of_isSolvable_quotient [Group.IsPerfect G] {C : Subgroup G} [C.Normal]
    (h : Group.IsSolvable (G ⧸ C)) : C = ⊤ := by
  by_contra hC
  have : Nontrivial (G ⧸ C) := QuotientGroup.nontrivial_iff.mpr hC
  exact Group.IsPerfect.not_isSolvable (G ⧸ C) h

theorem eq_top_of_not_le [Group.IsPerfect G] {K : Subgroup G} [K.Normal] [IsSimpleGroup (G ⧸ K)]
    (hK : Group.IsSolvable K) {C : Subgroup G} [hC : C.Normal] (hCK : ¬ C ≤ K) : C = ⊤ := by
  have hM : (C.map (QuotientGroup.mk' K)).Normal := hC.map _ (QuotientGroup.mk'_surjective K)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' K)) with h | h
  · exact absurd (by rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h) hCK
  ·
    refine eq_top_of_isSolvable_quotient ?_
    have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp K.subtype) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H g =>
        have hg : QuotientGroup.mk' K g ∈ C.map (QuotientGroup.mk' K) := by
          rw [h]
          trivial
        obtain ⟨c, hc, hcg⟩ := hg
        have hk : c⁻¹ * g ∈ K := QuotientGroup.eq.mp hcg
        refine ⟨⟨c⁻¹ * g, hk⟩, ?_⟩
        change (QuotientGroup.mk (c⁻¹ * g) : G ⧸ C) = QuotientGroup.mk g
        rw [QuotientGroup.eq, show (c⁻¹ * g)⁻¹ * g = g⁻¹ * c * g by group]
        exact hC.conj_mem' c hc g
    exact Group.isSolvable_of_surjective hsurj

theorem exists_centralizer_pCore_le [Finite G] [Group.IsPerfect G] {K : Subgroup G} [K.Normal]
    [IsSimpleGroup (G ⧸ K)] (hK : Group.IsSolvable K) (hq : ¬ IsQuasisimple G) :
    ∃ p : ℕ, p.Prime ∧ Subgroup.centralizer (pCore p G : Set G) ≤ K := by
  by_contra h
  push Not at h
  have hcen : ∀ p : ℕ, p.Prime → pCore p G ≤ Subgroup.center G := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    have : (pCore p G).Normal := pCore_normal
    have : (Subgroup.centralizer (pCore p G : Set G)).Normal := inferInstance
    have htop := eq_top_of_not_le hK (h p hp)
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (pCore p G : Set G) := by
      rw [htop]
      trivial
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have hpK : ∀ p : (Nat.card K).primeFactors,
      (pCore (p : ℕ) K).map K.subtype ≤ Subgroup.center G := by
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have : Fact (p : ℕ).Prime := ⟨hp⟩
    have hnorm : ((pCore (p : ℕ) K).map K.subtype).Normal := inferInstance
    have hpg : IsPGroup (p : ℕ) ((pCore (p : ℕ) K).map K.subtype) :=
      pCore_isPGroup.map K.subtype
    exact (le_sSup ⟨hnorm, hpg⟩ : _ ≤ pCore (p : ℕ) G).trans (hcen p hp)
  have hFK : (fittingSubgroup K).map K.subtype ≤ Subgroup.center G := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    exact iSup_le hpK
  have hFKc : fittingSubgroup K ≤ Subgroup.center K := fun x hx =>
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext ((Subgroup.mem_center_iff.mp (hFK ⟨x, hx, rfl⟩)) g)
  have htopF : fittingSubgroup K = ⊤ := by
    refine top_le_iff.mp (le_trans (fun g _ => ?_)
      (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hK))
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => (Subgroup.mem_center_iff.mp (hFKc hh) g).symm
  have hKc : K ≤ Subgroup.center G := fun x hx => by
    have hx' : (⟨x, hx⟩ : K) ∈ fittingSubgroup K := by
      rw [htopF]
      trivial
    exact hFK ⟨⟨x, hx⟩, hx', rfl⟩
  have hcK : Subgroup.center G ≤ K :=
    le_of_isSolvable_of_normal inferInstance inferInstance
  have hKZ : K = Subgroup.center G := le_antisymm hKc hcK
  apply hq
  have hsimp : IsSimpleGroup (G ⧸ Subgroup.center G) :=
    (QuotientGroup.quotientMulEquivOfEq hKZ).symm.isSimpleGroup
  refine ⟨inferInstance, hsimp, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative (G ⧸ Subgroup.center G) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (G ⧸ Subgroup.center G) this

end CFSG.RankThree.PartTwo.Sec4.Census
