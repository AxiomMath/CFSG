module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceTypes
public import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem isSolvable_vertex_of_oTwoQuot [Finite G] {L : Subgroup G}
    (h : Group.IsSolvable (oTwoQuot ↥L)) : Group.IsSolvable ↥L := by
  have : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥L) :=
    F1.isSolvable_of_isPGroup_two (CFSG.LieType.BorelTits.pCore_isPGroup 2)
  refine Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 ↥L).subtype
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

theorem isSolvable_oTwoQuot_of_vertex {L : Subgroup G} (h : Group.IsSolvable ↥L) :
    Group.IsSolvable (oTwoQuot ↥L) :=
  Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥L))

theorem VBig.not_isSolvable [Finite G] {L : Subgroup G} (hL : IsRankOneListed (oTwoQuot ↥L))
    (h : VBig L) : ¬ Group.IsSolvable ↥L := fun hs =>
  h ((isSmallListed_iff_isSolvable hL).2 (isSolvable_oTwoQuot_of_vertex hs))

theorem vBig_of_not_isSolvable [Finite G] {L : Subgroup G} (h : ¬ Group.IsSolvable ↥L) :
    VBig L := fun hs => h (isSolvable_vertex_of_oTwoQuot (IsSmallListed.isSolvable hs))

theorem vBig_iff_not_isSolvable [Finite G] {L : Subgroup G}
    (hL : IsRankOneListed (oTwoQuot ↥L)) : VBig L ↔ ¬ Group.IsSolvable ↥L :=
  ⟨VBig.not_isSolvable hL, vBig_of_not_isSolvable⟩

theorem F112Hyp.vBig_iff_left [Finite G] {L1 L2 S : Subgroup G} (h : F112Hyp L1 L2 S) :
    VBig L1 ↔ ¬ Group.IsSolvable ↥L1 :=
  vBig_iff_not_isSolvable h.1.h1.listed

theorem F112Hyp.vBig_iff_right [Finite G] {L1 L2 S : Subgroup G} (h : F112Hyp L1 L2 S) :
    VBig L2 ↔ ¬ Group.IsSolvable ↥L2 :=
  vBig_iff_not_isSolvable h.1.h2.listed

end CFSG.Quasithin
