module

public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartOne.F106.NcTheta
import CFSG.RankThree.PartOne.S10.FiveCriticalCentralInvolution
import CFSG.RankThree.PartOne.S10.FiveCriticalOddCore
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergBMScalarActionQuasisimpleQuotient
import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.FiveCritical
open scoped commutatorElement

theorem commutator_zpowers_le_oddThetaCore {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    {c : G} {q : ℕ} {D R : Subgroup G} (hcrit : FiveCriticalData A L c q D R) {z : G}
    (hzR : z ∈ R) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hzinv : ∀ d ∈ D, z * d * z⁻¹ * d ∈ inSubgroup frattini D) :
    ⁅L, zpowers z⁆ ≤ oddThetaCore 5 L := by
  have hp : Nat.Prime 5 := by norm_num
  have hq := hcrit.q_prime
  have hLc : L ∈ thetaComponentsAt 5 c := hcrit.mem_family.2
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsAt hLc
  have hLL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLperf
  have hzL : z ∈ L := hcrit.R_le_L hzR
  have hLD : L ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf Subgroup.le_normalizer hcrit.D_le_L hcrit.D_char
  have hDq : IsPGroup q D := fun g => ⟨1, Subtype.ext (by simpa using hcrit.D_exponent g g.2)⟩
  have hLDc : ⁅L, D⁆ ≠ ⊥ := fun h =>
    hcrit.R_acts (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hcrit.R_le_L le_rfl))
  have hz2ord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hscalar : ∀ b ∈ zpowers z, ∃ k : ℕ, ∀ d ∈ D,
      (b * d * b⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D := by
    intro b hb
    rcases (SteinbergBY.mem_zpowers_of_orderOf_eq_two hz2ord).mp hb with rfl | rfl
    · refine ⟨1, fun d hd => ?_⟩
      simp only [one_mul, inv_one, mul_one, pow_one, inv_mul_cancel]
      exact one_mem _
    · exact ⟨q - 1, scalar_pred_of_inverts hq hcrit.D_exponent (hLD hzL) hzinv⟩
  have hOLsol := oddThetaCore_subgroupOf_isSolvable hp L
  have hOsol : Group.IsSolvable (oddThetaCore 5 L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (oddThetaCore_le 5 L)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (oddThetaCore_le 5 L)).symm.injective
  have := hcrit.odd_normal
  exact SteinbergBM.scalar_critical_action_centralizes_quasisimple_solvable_quotient hq hLL hOsol
    hcrit.odd_quotient_quasisimple hLD hDq hLDc
    (zpowers_le.mpr (Subgroup.le_normalizer hzL)) (zpowers_le.mpr (hLD hzL)) hscalar

theorem z_mem_core_of_le {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G} {q : ℕ}
    {D R : Subgroup G} (hcrit : FiveCriticalData A L c q D R) {z : G} (hzR : z ∈ R) (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hzinv : ∀ d ∈ D, z * d * z⁻¹ * d ∈ inSubgroup frattini D)
    {P : Subgroup G} (hPL : P ≤ L) (hzP : z ∈ P) :
    z ∈ inSubgroup (aschbacherSolvableCore 5) P := by
  have hp : Nat.Prime 5 := by norm_num
  have hcomm := commutator_zpowers_le_oddThetaCore hcrit hzR hz1 hz2 hzinv
  have hz2ord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  set O := oddThetaCore 5 L with hO
  have hOL : O ≤ L := oddThetaCore_le 5 L
  have hOn : (O.subgroupOf L).Normal := oddThetaCore_subgroupOf_normal 5 L
  have hzg : ∀ g ∈ P, ⁅z, g⁆ ∈ O := fun g hg => by
    have h := hcomm (Subgroup.commutator_mem_commutator (hPL hg) (mem_zpowers z))
    rw [← commutatorElement_inv]
    exact O.inv_mem h
  set Q : Subgroup ↥P := O.subgroupOf P with hQ
  have hQn : Q.Normal := by
    have h := hOn.comap (Subgroup.inclusion hPL)
    rwa [Subgroup.comap_inclusion_subgroupOf] at h
  let φ : Q →* O := (P.subtype.comp Q.subtype).codRestrict O fun q => q.2
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun w : O => (w : G)) h))
  have hOLsol := oddThetaCore_subgroupOf_isSolvable hp L
  have hOsol : Group.IsSolvable O :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hOL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hOL).symm.injective
  have hQs : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective hφ
  have hQp : ¬ 5 ∣ Nat.card Q := by
    intro h
    refine oddThetaCore_subgroupOf_not_dvd hp L ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOL).toEquiv]
    exact h.trans (Subgroup.card_dvd_of_injective φ hφ)
  obtain ⟨-, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization (H := ↥P) hp
  have hQθ : Q ≤ aschbacherSolvableCore 5 ↥P := hmax Q hQn hQs hQp
  have hmem : (⟨z, hzP⟩ : ↥P) ∈ aschbacherSolvableCore 5 ↥P := by
    refine mem_aschbacherSolvableCore_of_commutator_mem hp _ ?_ fun g => hQθ ?_
    · rw [Subgroup.orderOf_mk, hz2ord]
      norm_num
    · show ((⁅(⟨z, hzP⟩ : ↥P), g⁆ : ↥P) : G) ∈ O
      have h : ((⁅(⟨z, hzP⟩ : ↥P), g⁆ : ↥P) : G) = ⁅z, (g : G)⁆ := by
        simp [commutatorElement_def]
      rw [h]
      exact hzg g g.2
  exact ⟨⟨z, hzP⟩, hmem, rfl⟩

end CFSG.RankThree.PartOne.F106
