module

public import CFSG.RankThree.PartTwo.Sec17.PropUStepThree

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17
  CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_Rstar {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {A R T : Subgroup G}
    (hT : IsPGroup p T) (hRT : R ≤ T) (hTN : T ≤ Subgroup.normalizer (R : Set G)) (hR1 : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    ∃ Rs : Subgroup G, Rs ≤ R ∧ Rs ≠ ⊥ ∧ T ≤ Subgroup.centralizer (Rs : Set G) ∧
      A ≤ Subgroup.normalizer (Rs : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  refine ⟨R ⊓ Subgroup.centralizer (T : Set G), inf_le_left, ?_, ?_, ?_⟩
  · haveI : (R.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRT).mpr hTN
    have hRsub : R.subgroupOf T ≠ ⊥ := by
      intro h
      apply hR1
      refine eq_bot_iff.mpr fun x hx => ?_
      have hx' : (⟨x, hRT hx⟩ : ↥T) ∈ R.subgroupOf T := Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      simpa using congrArg Subtype.val hx'
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hRsub)
    have hzR : ((z : ↥T) : G) ∈ R := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
    have hzC : (z : ↥T) ∈ Subgroup.center ↥T := (Subgroup.mem_inf.mp z.2).2
    have hzT : ∀ h ∈ T, h * ((z : ↥T) : G) = ((z : ↥T) : G) * h := fun h hh => by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC ⟨h, hh⟩)
      simpa using this
    have hwne : ((z : ↥T) : G) ≠ 1 := by
      intro h
      apply hz1
      exact Subtype.ext (by simpa using h)
    intro hbot
    have hmem : ((z : ↥T) : G) ∈ R ⊓ Subgroup.centralizer (T : Set G) :=
      Subgroup.mem_inf.mpr ⟨hzR, Subgroup.mem_centralizer_iff.mpr fun h hh =>
        hzT h (SetLike.mem_coe.mp hh)⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hwne hmem
  · intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : s ∈ R ⊓ Subgroup.centralizer (T : Set G) := SetLike.mem_coe.mp hs
    have hsC : s ∈ Subgroup.centralizer (T : Set G) := (Subgroup.mem_inf.mp hs').2
    rw [Subgroup.mem_centralizer_iff] at hsC
    exact (hsC t ht).symm
  · exact CFSG.RankThree.PartTwo.Sec17.PropU.pu_le_normalizer_inf hAR
      (CFSG.RankThree.PartTwo.Sec17.PropU.le_normalizer_centralizer_of hAT)

theorem normalizer_mem_scriptY {G : Type} [Group G] [Finite G] (hG : TheoremFourHyp G) {p : ℕ}
    (hp : p.Prime) {A Rs : Subgroup G} (hR : IsPGroup p Rs) (hR1 : Rs ≠ ⊥)
    (hA : A ≤ Subgroup.normalizer (Rs : Set G)) :
    Subgroup.normalizer (Rs : Set G) ∈ scriptY A := by
  haveI : IsSimpleGroup G := hG.isSimpleGroup
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [scriptY, Set.mem_setOf_eq]
  refine ⟨?_, hA.trans Subgroup.le_normalizer⟩
  intro htop
  haveI : Rs.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Rs with h | h
  · exact hR1 h
  · subst h
    haveI : Group.IsNilpotent G := Group.isNilpotent_top.mp hR.isNilpotent
    obtain ⟨a, b, hab⟩ := hG.nonabelian
    exact hab (mul_comm a b)

end CFSG.RankThree.PartTwo.Sec17.PropU
