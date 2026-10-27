module

public import CFSG.RankThree.PartTwo.Sec13.K135OutTwoTower

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem ot_cyclic_mod_of_isCyclic_quotient {G : Type*} [Group G] (D I : Subgroup G) [I.Normal]
    (h : IsCyclic (↥D ⧸ I.subgroupOf D)) : ∃ g ∈ D, ∀ x ∈ D, ∃ k : ℤ, g ^ k * x ∈ I := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := ↥D ⧸ I.subgroupOf D)
  obtain ⟨⟨g, hgD⟩, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨g, hgD, fun x hx => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hc (QuotientGroup.mk ⟨x, hx⟩))
  refine ⟨-m, ?_⟩
  have h1 : (QuotientGroup.mk ((⟨g, hgD⟩ : ↥D) ^ (-m) * ⟨x, hx⟩) :
      ↥D ⧸ I.subgroupOf D) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, zpow_neg, ← hm, inv_mul_cancel]
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_subgroupOf.mp h2

theorem outTwoGen_of_hom_cyclic {X : Type*} [Group X] [Finite X] {C : Type*} [Group C] [IsCyclic C]
    (Θ : MulAut X →* C)
    (hb : ∃ g₁ ∈ Θ.ker, ∀ x ∈ Θ.ker, ∃ k : ℤ,
      g₁ ^ k * x ∈ (MulAut.conj : X →* MulAut X).range) :
    OutTwoGen X := by
  haveI : ((MulAut.conj : X →* MulAut X).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal X
  refine outTwoGen_of_tower (MulAut.conj : X →* MulAut X).range Θ.ker
    (fun δ hδ _ _ => hδ) hb ?_
  haveI : IsCyclic ↥Θ.range := Subgroup.isCyclic Θ.range
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥Θ.range)
  obtain ⟨g₂, hg₂⟩ := γ.2
  refine ⟨g₂, fun x => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨Θ x, ⟨x, rfl⟩⟩)
  refine ⟨-m, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_zpow, hg₂, zpow_neg]
  have h1 : (γ : C) ^ m = Θ x := by
    have h := congrArg Subtype.val hm
    rw [Subgroup.coe_zpow] at h
    exact h
  rw [h1, inv_mul_cancel]

end CFSG.RankThree.PartTwo.Sec13.F135Last
