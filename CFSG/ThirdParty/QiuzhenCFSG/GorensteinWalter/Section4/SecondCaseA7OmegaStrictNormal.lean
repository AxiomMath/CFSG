module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaStrictIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaFNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Normality in the strict A7 omega branch -/

open scoped commutatorElement

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If `K F` is properly contained in the second center omega subgroup, then
it is normal in `F(U)`. -/
public theorem secondCase_a7_omega_strict_normal
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (hAltQ : od.K ⊔ od.F < od.Q.map c.FU.subtype) :
    IsNormalIn (od.K ⊔ od.F) c.FU := by
  classical
  let A : Subgroup G := od.K ⊔ od.F
  let QG : Subgroup G := od.Q.map c.FU.subtype
  have hAleQ : A ≤ QG := hAltQ.le
  have hQGleFU : QG ≤ c.FU := Subgroup.map_subtype_le od.Q
  let FQ : Subgroup QG := od.F.subgroupOf QG
  let AQ : Subgroup QG := A.subgroupOf QG
  have hnormFQ : Subgroup.normalizer (FQ : Set QG) = AQ := by
    simpa [A, QG, FQ, AQ] using
      secondCase_a7_omega_normalizer_F_eq c w d od hAleQ
  have hZQleAQ : Subgroup.center QG ≤ AQ := by
    rw [← hnormFQ]
    exact Subgroup.center_le_normalizer (FQ : Set QG)
  let ZG : Subgroup G := (Subgroup.center QG).map QG.subtype
  have hZGleA : ZG ≤ A := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨zq, hzq, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hZQleAQ hzq)
  have hQnormalU : IsNormalIn QG c.U := by
    exact map_characteristic_isNormalIn_of_isNormalIn od.Q
      od.Q_characteristic (fittingSubgroupOf_isNormalIn c.U)
  refine ⟨hAleQ.trans hQGleFU, ?_⟩
  intro u hu a ha
  have haQ : a ∈ QG := hAleQ ha
  rcases Subgroup.mem_map.mp haQ with ⟨a0, ha0, ha0val⟩
  let aR : c.FU := ⟨a, hQGleFU haQ⟩
  let uR : c.FU := ⟨u, hu⟩
  have haRZ2 : aR ∈ Subgroup.upperCentralSeries c.FU 2 := by
    have ha0Z2 := od.Q_le_upperCentralSeries_two ha0
    have haReq : aR = a0 := Subtype.ext ha0val.symm
    rw [haReq]
    exact ha0Z2
  have hcommCenter : ⁅aR, uR⁆ ∈ Subgroup.center c.FU := by
    have hstep :=
      (Subgroup.mem_upperCentralSeries_succ_iff
        (G := c.FU) (n := 1) (x := aR)).mp haRZ2 uR
    simpa [Subgroup.upperCentralSeries_one, commutatorElement_def] using hstep
  let z : G := a * u * a⁻¹ * u⁻¹
  have hzCentFU : z ∈ Subgroup.centralizer (c.FU : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yR : c.FU := ⟨y, hy⟩
    have hcomm := (Subgroup.mem_center_iff.mp hcommCenter) yR
    exact congrArg Subtype.val hcomm
  have hzQ : z ∈ QG := by
    have huU : u ∈ c.U := fittingSubgroupOf_le c.U hu
    have hconjInvQ : u * a⁻¹ * u⁻¹ ∈ QG :=
      hQnormalU.2 u huU a⁻¹ (QG.inv_mem haQ)
    dsimp [z]
    simpa [mul_assoc] using QG.mul_mem haQ hconjInvQ
  have hzZG : z ∈ ZG := by
    let zQ : QG := ⟨z, hzQ⟩
    apply Subgroup.mem_map.mpr
    refine ⟨zQ, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hzCentFU) (q : G) (hQGleFU q.2)
  have hzA : z ∈ A := hZGleA hzZG
  have hconj : u * a * u⁻¹ = z⁻¹ * a := by
    dsimp [z]
    group
  rw [hconj]
  exact A.mul_mem (A.inv_mem hzA) ha

end CFSG.GorensteinWalter
