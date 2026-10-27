module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofComp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringUnitary

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem isComponent_map_rangeRestrict {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    {K : Subgroup P} (hK : IsComponent K) (hinj : Function.Injective (f.comp K.subtype)) :
    IsComponent (K.map f.rangeRestrict) := by
  have hinj' : Function.Injective (f.rangeRestrict.comp K.subtype) := by
    intro x y hxy
    apply hinj
    have := congrArg Subtype.val hxy
    exact this
  have hrange : (f.rangeRestrict.comp K.subtype).range = K.map f.rangeRestrict := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨?_, Subgroup.IsSubnormal.map f.rangeRestrict_surjective hK.2⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange)) hK.1

theorem isComponent_map_subgroupOf_range {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    {K : Subgroup P} (hK : IsComponent K) (hinj : Function.Injective (f.comp K.subtype)) :
    IsComponent ((K.map f).subgroupOf f.range) := by
  have h := isComponent_map_rangeRestrict f hK hinj
  have heq : (K.map f).subgroupOf f.range = K.map f.rangeRestrict := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, hkx⟩
      exact ⟨k, hk, Subtype.ext hkx⟩
    · rintro ⟨k, hk, hkx⟩
      exact ⟨k, hk, congrArg Subtype.val hkx⟩
  rwa [heq]

theorem isComponent_subgroupOf_congr {Y : Type*} [Group Y] {A B K : Subgroup Y} (h : A = B)
    (hK : IsComponent (K.subgroupOf A)) : IsComponent (K.subgroupOf B) := by
  subst h
  exact hK

end CFSG.RankThree.PartTwo.Sec4.HeringUnitary
