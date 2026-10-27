module

public import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110FieldEq
public import CFSG.Open.StatedDefs
public import CFSG.CGT.Timmesfeld75.SLTransvection
import CFSG.GroupTheory.CentralQuotientLift
import CFSG.Quasithin.Background.SmithA36Lift
import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar
import CFSG.RankThree.GF2n.Stroth80.Sec11CM
import CFSG.RankThree.GF2n.Stroth80.Sec112Basic
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.HeringSec118Center
import CFSG.Adapters.StatedSLPerfect
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
import CFSG.Certificates.CosetTableShort
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import Certificates.Certificate2154
import Certificates.Certificate2157
import Certificates.Certificate3008

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem Ctx.exists_slHom_Xbar (hc : Ctx M Q Z B) {m : ℕ} (hm : 3 ≤ m)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)) :
    ∃ σ : SL(m, K) →* ↥(Xbar M Q Z B),
      ∀ g, CFSG.ComponentClassification.RankTwoClassical.modelHom e (σ g) = proj m K g := by
  have hm3 : 3 ≤ m := hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm' : 2 ≤ m' := by omega
  have hsplit : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (SL(m' + 1, K)) := by
    intro E _ _ π hπ hcen hodd
    exact CFSG.Quasithin.SmithA36.sl_exists_section_of_charTwo hm' hπ hcen
      (fun z hz => hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard π.ker hz))
  obtain ⟨σ, hσ⟩ :=
    CFSG.GroupTheory.exists_lift_of_oddCentralSplit hsplit
      (CFSG.ComponentClassification.RankTwoClassical.modelHom_surjective (e := e))
      (by rw [CFSG.ComponentClassification.RankTwoClassical.ker_modelHom])
      (by
        rw [CFSG.ComponentClassification.RankTwoClassical.ker_modelHom]
        exact hc.odd_card_center_Xbar)
      (proj (m' + 1) K)
  exact ⟨σ, fun g => by simpa using DFunLike.congr_fun hσ g⟩

theorem Ctx.slHom_Xbar_surjective (hc : Ctx M Q Z B) {m : ℕ} (hm : 3 ≤ m)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)} {σ : SL(m, K) →* ↥(Xbar M Q Z B)}
    (hσ : ∀ g, CFSG.ComponentClassification.RankTwoClassical.modelHom e (σ g) = proj m K g) :
    Function.Surjective σ := by
  have hSL : Group.IsPerfect (StatedSL m K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hm K
  have hProj : Group.IsPerfect (StatedProj (StatedSL m K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hperf : Group.IsPerfect (XbarMod M Q Z B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hX : Group.IsPerfect ↥(Xbar M Q Z B) :=
    Group.isPerfect_def.mpr (hc.commutator_Xbar_eq_top_of_isPerfect_xbarMod hperf)
  have hker : (CFSG.ComponentClassification.RankTwoClassical.modelHom e).ker ≤
      Subgroup.center ↥(Xbar M Q Z B) := by
    rw [CFSG.ComponentClassification.RankTwoClassical.ker_modelHom]
  refine surjective_of_perfect_of_central_ker
    (CFSG.ComponentClassification.RankTwoClassical.modelHom e) hker σ ?_
  have hcomp : ((CFSG.ComponentClassification.RankTwoClassical.modelHom e).comp σ) = proj m K :=
    MonoidHom.ext hσ
  rw [hcomp]
  exact proj_surjective m K

theorem Ctx.exists_isTransvection_slHom_eq (hc : Ctx M Q Z B) {m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)} {σ : SL(m, K) →* ↥(Xbar M Q Z B)}
    (hσ : ∀ g, CFSG.ComponentClassification.RankTwoClassical.modelHom e (σ g) = proj m K g)
    {a : ↥M} (ha : (a : G) ∈ LB M Q B) (hA2 : IsA2 Q Z (a : G)) :
    ∃ A : SL(m, K), IsTransvection A ∧
      σ A = ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a ha hA2⟩ := by
  let aX : ↥(Xbar M Q Z B) :=
    ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a ha hA2⟩
  have hEa : (aX : Mbar M Q) ∈ Ebar M Q Z B := hc.mk_mem_Ebar ha hA2
  have haX2 : aX * aX = 1 := by
    apply Subtype.ext
    have h2 : orderOf (aX : Mbar M Q) = 2 := by
      have h := Ctx.orderOf_eq_two_of_mem_A2Set (Ctx.mk_mem_A2Set a.2 hA2)
      simpa [aX] using h
    have h3 := pow_orderOf_eq_one (aX : Mbar M Q)
    rw [h2] at h3
    simpa [pow_two] using h3
  have himg2 : CFSG.ComponentClassification.RankTwoClassical.modelHom e aX *
      CFSG.ComponentClassification.RankTwoClassical.modelHom e aX = 1 := by
    rw [← map_mul, haX2, map_one]
  obtain ⟨A, hprojA, hA2A⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.exists_sl_lift
      (CFSG.ComponentClassification.RankTwoClassical.modelHom e aX) himg2
  have hAtv : IsTransvection A :=
    Ctx.isTransvection_of_modelHom_eq hc hEa hA2A hprojA.symm
  have hker : (CFSG.ComponentClassification.RankTwoClassical.modelHom e).ker ≤
      Subgroup.center ↥(Xbar M Q Z B) := by
    rw [CFSG.ComponentClassification.RankTwoClassical.ker_modelHom]
  have hodd : Odd (Nat.card
      (CFSG.ComponentClassification.RankTwoClassical.modelHom e).ker) := by
    rw [CFSG.ComponentClassification.RankTwoClassical.ker_modelHom]
    exact hc.odd_card_center_Xbar
  have hσA : σ A = aX :=
    eq_of_involution_lift (CFSG.ComponentClassification.RankTwoClassical.modelHom e) hker hodd
      (by rw [← map_mul, hA2A, map_one]) haX2 (by rw [hσ A, hprojA])
  exact ⟨A, hAtv, hσA⟩

end CFSG.RankThree.GF2n.Stroth80
