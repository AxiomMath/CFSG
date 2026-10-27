module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem invPartF_holds : InvPartF := by
  intro G _ _ Y X hXY hX3 tb htb hinv
  have hX' : IsPGroup 3 (X.subgroupOf Y) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hX3 _ (Subgroup.mem_subgroupOf.mp x.2)
  have hN := normalizer_map_mk_eq hX'
  rw [hN] at htb
  obtain ⟨t, ht, rfl⟩ := htb
  refine ⟨(t : G), t.2, fun x hx => ?_⟩
  have hxY : x ∈ Y := hXY hx
  have hx' : (⟨x, hxY⟩ : Y) ∈ X.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx
  have h1 : t * ⟨x, hxY⟩ * t⁻¹ ∈ X.subgroupOf Y := (Subgroup.mem_normalizer_iff.mp ht _).mp hx'
  have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (t * ⟨x, hxY⟩ * t⁻¹) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (⟨x, hxY⟩ : Y)⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact hinv _ (Subgroup.mem_map_of_mem _ hx')
  have h3 := injOn_mk_of_isPGroup Nat.prime_three hX' h1 (inv_mem hx') h2
  exact congrArg Subtype.val h3

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
