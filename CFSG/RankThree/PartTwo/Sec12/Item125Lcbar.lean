module

import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec12.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {c : G} {L : Subgroup G}

theorem mem_thetaQuotCentralizer_of_mk_mem_centralizer (hL : L ∈ thetaComponentsAt 3 c)
    {z : Subgroup.normalizer (Subgroup.zpowers c : Set G)}
    (hz : QuotientGroup.mk' _ z ∈ Subgroup.centralizer ((lBar c L : Subgroup _) : Set
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))))) :
    (z : G) ∈ Sec4.thetaQuotCentralizer L := by
  have hLH : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Sec13.le_normalizer_zpowers_of_mem hL
  have hst := theta_component_quotient_structure Nat.prime_three
    (Sec13.subgroupOf_normalizer_mem_thetaComponents hL)
  have hzN : z ∈ Subgroup.normalizer ((L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c :
      Set G)) : Subgroup _) : Set (Subgroup.normalizer (Subgroup.zpowers c : Set G))) := by
    rw [hst.2.2.2.2.2.1, Subgroup.mem_comap]
    exact Subgroup.centralizer_le_normalizer _ hz
  have hzL : (z : G) ∈ Subgroup.normalizer (L : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hzN ⟨x, hLH hx⟩).mp
      (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp h1
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hzL, fun l hl => ?_⟩
  set l₁ : Subgroup.normalizer (Subgroup.zpowers c : Set G) := ⟨l, hLH hl⟩
  have hl₁ : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) l₁ ∈ lBar c L :=
    ⟨l₁, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hx : l₁⁻¹ * (z * l₁ * z⁻¹) ∈
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul,
      map_inv, map_inv, (Subgroup.mem_centralizer_iff.mp hz _ hl₁).symm]
    group
  have hxN : l⁻¹ * ((z : G) * l * (z : G)⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := ⟨_, hx, rfl⟩
  have hxL : l⁻¹ * ((z : G) * l * (z : G)⁻¹) ∈ L :=
    L.mul_mem (L.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hzL l).mp hl)
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL, Sec13.inSubgroup_theta_centralizer]
  exact ⟨hxL, Sec6.le_centralizer_of_mem_thetaComponentsAt hL hxL, hxN⟩

theorem exists_mul_of_mem_lcBar (hL : L ∈ thetaComponentsAt 3 c) {g : G} (hg : g ∈ lcBar c L) :
    ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L, g = l * z := by
  obtain ⟨h, hh, rfl⟩ := hg
  have hle : Subgroup.centralizer ((lBar c L : Subgroup _) : Set
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) ≤
      Subgroup.normalizer ((lBar c L : Subgroup _) : Set _) :=
    Subgroup.centralizer_le_normalizer _
  have hmem : QuotientGroup.mk' _ h ∈ lBar c L ⊔ Subgroup.centralizer
      ((lBar c L : Subgroup _) : Set (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) := hh
  have hmem' := (SetLike.mem_coe).mpr hmem
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hmem'
  obtain ⟨x, ⟨l', hl', rfl⟩, y, hy, hxy⟩ := hmem'
  refine ⟨(l' : G), Subgroup.mem_subgroupOf.mp hl',
    ((l'⁻¹ * h : Subgroup.normalizer (Subgroup.zpowers c : Set G)) : G), ?_, ?_⟩
  · refine mem_thetaQuotCentralizer_of_mk_mem_centralizer hL ?_
    rw [map_mul, map_inv, ← hxy, inv_mul_cancel_left]
    exact hy
  · simp

theorem thetaQuotCentralizer_le_normalizer' (L : Subgroup G) :
    Sec4.thetaQuotCentralizer L ≤ Subgroup.normalizer (L : Set G) :=
  fun _ hx => (Sec6.mem_thetaQuotCentralizer_iff.mp hx).1

theorem lcBar_le_normalizer (hL : L ∈ thetaComponentsAt 3 c) :
    lcBar c L ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_of_mem_lcBar hL hg
  exact mul_mem (Subgroup.le_normalizer hl) (thetaQuotCentralizer_le_normalizer' L hz)

end CFSG.RankThree.PartTwo.Sec12
