module

import CFSG.GroupTheory.SteinbergBSNormalPlane
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.Planes

open Subgroup

variable {G : Type*} [Group G]

theorem map_subgroupOf_subtype {P H : Subgroup G} (hHP : H ≤ P) :
    (H.subgroupOf P).map P.subtype = H := by
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hHP]

theorem card_subgroupOf {P H : Subgroup G} (hHP : H ≤ P) :
    Nat.card (H.subgroupOf P) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv

theorem map_subtype_inf_centralizer {P V A : Subgroup G} (hAP : A ≤ P) (hVP : V ≤ P) :
    (A.subgroupOf P ⊓ centralizer ((V.subgroupOf P : Subgroup P) : Set P)).map P.subtype =
      A ⊓ centralizer (V : Set G) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hyC⟩, rfl⟩
    refine ⟨hyA, mem_centralizer_iff.2 fun h hh => ?_⟩
    exact congrArg Subtype.val (mem_centralizer_iff.1 hyC ⟨h, hVP hh⟩ hh)
  · rintro ⟨hxA, hxC⟩
    refine ⟨⟨x, hAP hxA⟩, ⟨hxA, mem_centralizer_iff.2 fun h hh => ?_⟩, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.1 hxC h.1 hh)

theorem normalPlane_concrete [Finite G] {p : ℕ} (hp : p.Prime) {P V A : Subgroup G}
    (hP : IsPGroup p P) (hVP : V ≤ P) (hVn : P ≤ normalizer (V : Set G))
    (hV : IsElementaryAbelian p V) (hVc : Nat.card V = p ^ 2)
    (hAP : A ≤ P) (hA : IsElementaryAbelian p A) (hAc : Nat.card A = p ^ 3) :
    p ^ 2 ≤ Nat.card ↥(A ⊓ centralizer (V : Set G)) ∧
      p ^ 3 ≤ Nat.card ↥((A ⊓ centralizer (V : Set G)) ⊔ V) := by
  have hpF : Fact p.Prime := ⟨hp⟩
  have hVnormal : (V.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVP).2 hVn
  have hV' : IsElementaryAbelian p (V.subgroupOf P) := IsElementaryAbelian.subgroupOf hVP
  have hA' : IsElementaryAbelian p (A.subgroupOf P) := IsElementaryAbelian.subgroupOf hAP
  obtain ⟨-, -, -, hB, -, -, -, hU, -⟩ :=
    CFSG.GroupTheory.SteinbergBS.normal_plane_centralizer_rank_three hP (V.subgroupOf P)
      (A.subgroupOf P) (by rw [card_subgroupOf hVP, hVc]) (by rw [card_subgroupOf hAP, hAc])
  have hmap := map_subtype_inf_centralizer hAP hVP
  have hinj : Function.Injective P.subtype := Subtype.val_injective
  refine ⟨?_, ?_⟩
  · rw [← hmap, Subgroup.card_map_of_injective hinj]
    exact hB
  · have hsup : ((A.subgroupOf P ⊓ centralizer ((V.subgroupOf P : Subgroup P) : Set P)) ⊔
        V.subgroupOf P).map P.subtype = (A ⊓ centralizer (V : Set G)) ⊔ V := by
      rw [Subgroup.map_sup, hmap, map_subgroupOf_subtype hVP]
    rw [← hsup, Subgroup.card_map_of_injective hinj]
    exact hU

end CFSG.RankThree.PartOne.Planes
