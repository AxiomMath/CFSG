module

public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartDerive
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2HeartBI1 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → ∀ {labL : LargeEvenLabel}, labL.tag = .twE6 →
      GGLabQTwo 3 labL → LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) →
        ∀ M : GGQ2LDatum 3 Bs L x, GGQ2LabelWeyl labL M.coxeter → M.ShapeB → GGQTwoI1 Bs D J

theorem ggQ2HeartBI1_of_cent (hJ : GGQ2HeartJCentralizes) :
    GGQ2HeartBI1 := by
  intro G _ _ B Bs x L D J hS labL htag _ hmark M hW hB
  exact ggQ2_heartB_i1 hJ hS htag hmark M hW hB

end CFSG.StandardType

end
