module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2A
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6


theorem C11P9A.range_simpleRootSL2_le_parabolic {τ : Tag} {K : Type} [Field K]
    (i : Fin τ.rank) : (simpleRootSL2 τ K i).range ≤ parabolicSubgroup τ K {i} := by
  rw [range_simpleRootSL2, Subgroup.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact posWeylGroup_le_parabolicSubgroup_singleton i
      (posUnipotent_le_posWeylGroup i (xUnit_mem_posUnipotent i c))
  · exact posWeylGroup_le_parabolicSubgroup_singleton i (yUnit_mem_posWeylGroup i c)

theorem factG2FourParabNonsolv_holds : FactG2FourParabNonsolv := by
  intro K _ _ _ hK j hsol
  have hK4 : ∃ s : Finset K, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hK.ge
  set i := g2Index j
  have hle := C11P9A.range_simpleRootSL2_le_parabolic (K := K) i
  have hPC := parabolicSubgroup_le_adjointGroup Tag.G2 K {i}
  have hP : Group.IsSolvable ↥(parabolicSubgroup Tag.G2 K {i}) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hPC).symm.toMonoidHom) (MulEquiv.injective _)
  have hSL : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion hle).comp (simpleRootSL2 Tag.G2 K i).rangeRestrict)
      (fun A B h => CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo i
        (congrArg Subtype.val (Subgroup.inclusion_injective hle h)))
  obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian (K := K) hK4
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K) := ⟨⟨a * b, b * a, hab⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
    (G := Matrix.SpecialLinearGroup (Fin 2) K)).ne
    (Group.isPerfect_def.mp (CFSG.LinearGroups.special_linear_dimension_two_perfect hK4))

end CFSG.Quasithin.Vol2.Ch11.SecS
