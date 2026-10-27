module

public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.GH74.GLS

variable {G : Type*} [Group G] (A : Subgroup G) (LB : Subgroup G → Subgroup G)

@[expose] def Item147 : Prop :=
  ∀ Y ∈ scriptY A, ⁅deltaZero A LB Y, pPrimeCoreOf 3 Y⁆ ≤ delta A LB (pPrimeCoreOf 3 Y)

@[expose] def Item148Normal : Prop :=
  ∀ Y ∈ scriptY A,
    (((deltaZero A LB Y).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal

@[expose] def Item149 : Prop :=
  ∀ Y ∈ scriptY A,
    oPrimeResidualOf 3 (delta A LB Y) =
        oPrimeResidualOf 3 (inSubgroup (oResidual 2) (deltaZero A LB Y)) ∧
      ((oPrimeResidualOf 3 (inSubgroup (oResidual 2) (deltaZero A LB Y))).subgroupOf Y).Normal ∧
      ((inSubgroup (oResidual 2) (deltaZero A LB Y)).subgroupOf
        (CFSG.Open.pCoreOf 2 Y ⊔ inSubgroup (oResidual 2) (deltaZero A LB Y))).Normal ∧
      (generalizedFitting ↥Y = CFSG.pCore 2 ↥Y →
        generalizedFitting ↥(inSubgroup (oResidual 2) (deltaZero A LB Y)) =
            CFSG.pCore 2 ↥(inSubgroup (oResidual 2) (deltaZero A LB Y)) ∧
          generalizedFitting ↥(deltaZero A LB Y) = CFSG.pCore 2 ↥(deltaZero A LB Y))

end CFSG.RankThree.PartTwo.Sec14
