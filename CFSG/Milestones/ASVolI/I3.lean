module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open

section Components

variable {G : Type} [Group G]

@[expose] def IsCComponentIn (L X : Subgroup G) : Prop :=
  L ≤ X ∧ CFSG.IsCComponent (L.subgroupOf X)

@[expose] def IsComponentIn (L X : Subgroup G) : Prop :=
  L ≤ X ∧ CFSG.IsQuasisimple ↥L ∧ (L.subgroupOf X).IsSubnormal

@[expose] def IsTwoComponentIn (L X : Subgroup G) : Prop :=
  IsCComponentIn L X ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L)

@[expose] def conjClosure (L Y : Subgroup G) : Subgroup G := ⨆ y ∈ Y, CFSG.conjugate L y

end Components

@[expose] def oddCoreE (H : Type) [Group H] : Subgroup H :=
  (CFSG.layer (H ⧸ CFSG.oddCore H)).comap (QuotientGroup.mk' (CFSG.oddCore H))

@[expose] def oddTwoCore (X : Type) [Group X] : Subgroup X :=
  (CFSG.pCore 2 (X ⧸ CFSG.oddCore X)).comap (QuotientGroup.mk' (CFSG.oddCore X))

scoped instance oddTwoCore_normal (X : Type) [Group X] : (oddTwoCore X).Normal := by
  unfold oddTwoCore
  infer_instance

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChIJK

@[expose] def I_3_1 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.SectionRank.IsKGroupCat H →
    ∀ P : Subgroup H, IsPGroup 2 P →
      ∀ L : Subgroup H, IsTwoComponentIn L (Subgroup.centralizer (P : Set H)) →
        ∃ K : Subgroup H,
          (IsTwoComponentIn K ⊤ ∧ conjClosure L (oddCoreE H) = conjClosure K P) ∧
          (L ≤ Subgroup.centralizer (CFSG.oddCore H : Set H) →
            IsComponentIn L (Subgroup.centralizer (P : Set H)) ∧ IsComponentIn K ⊤) ∧
          (CFSG.SectionRank.IsSQTKCat H → CFSG.pRank 3 ↥L = 2 →
            L ≤ K ∧ K.Normal ∧ CFSG.IsQuasisimple ↥L ∧ CFSG.IsQuasisimple ↥K)

@[expose] def I_3_2 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.SectionRank.IsKGroupCat H →
    ∀ t : H, t ^ 2 = 1 → t ≠ 1 →
      ∀ L : Subgroup H, IsTwoComponentIn L (Subgroup.centralizer ({t} : Set H)) →
        (IsTwoComponentIn (conjClosure L (oddCoreE H)) ⊤ ∧
          CFSG.conjugate (conjClosure L (oddCoreE H)) t = conjClosure L (oddCoreE H)) ∨
        (∃ J : Subgroup H, IsTwoComponentIn J ⊤ ∧ CFSG.conjugate J t ≠ J ∧
          conjClosure L (oddCoreE H) = J ⊔ CFSG.conjugate J t ∧
          Nonempty (↥J ⧸ oddTwoCore ↥J ≃* ↥L ⧸ oddTwoCore ↥L))

end CFSG.ASVolI
