module

public import CFSG.Monster.B.TwoA.Amalgam.CoverCensus
public import CFSG.Monster.B.TwoA.Amalgam.CoverAction
public import CFSG.Monster.B.TwoA.Amalgam.CoverNative
public import CFSG.Monster.B.TwoA.Amalgam.CentralExt
public import CFSG.Monster.B.Geometry.LocalBuildingCover

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding

theorem natCard_zpowers_cE'
    (hc : Nat.card (Subgroup.zpowers cQ) = 2) :
    Nat.card (Subgroup.zpowers cE') = 2 := by
  rw [← hc]
  have h : (Subgroup.zpowers cE').map Eam.subtype = Subgroup.zpowers cQ := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [← h]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).toEquiv

theorem ker_chamberLeft_eq
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ) :
    chamberLeft.ker = Subgroup.zpowers cE' := by
  ext g
  rw [mem_ker_chamberLeft_iff, hker, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [← hk]; rfl)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

theorem ncard_setOf_val_ne (m : ℕ) (hm : m < 4) :
    ({i : Fin Tag.F4.rank | (i : ℕ) ≠ m} : Set _).ncard = 3 := by
  rw [Set.ncard_eq_toFinset_card']
  interval_cases m <;> decide

theorem ncard_typesOff (i : Fin 4) : (typesOff i).ncard = 3 :=
  ncard_setOf_val_ne i i.2

variable (X : ChamberSystem (Fin Tag.F4.rank) Chamber)
  (hX : ∀ i c d, X.adj i c d ↔ chamberAdj i c d)

theorem universal_building_cover_of
    (hconn : X.Connected)
    (hpanel : ∀ (i : Fin Tag.F4.rank) (x : Chamber), ∃ y, y ≠ x ∧ X.adj i x y)
    (hres2 : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 2 → ∀ x,
      X.IsResidueBuilding (coxeterSystem .F4) J x)
    (hres3 : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 3 → ∀ x,
      X.IsResidueBuilding (coxeterSystem .F4) J x)
    (hsize : ∀ (i : Fin Tag.F4.rank) (x : Chamber),
      (X.residue {i} x).encard = if (i : ℕ) < 2 then 3 else 5)
    (hP1 : Pc 0 = ⨆ (j : Fin 4) (_ : j ≠ 0), Qam j)
    (hres : ∀ (J : Set (Fin Tag.F4.rank)) (g h : Eam), chamberOf h ∈ X.residue J (chamberOf g) ↔
      ((h * g⁻¹ : Eam) : Dfull) ∈ parJ J)
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    (hc : Nat.card (Subgroup.zpowers cQ) = 2) :
    (∃ δ : X.Cover (chamberOf 1) → X.Cover (chamberOf 1) → WeylGroup .F4,
      IsWeylDistanceBuilding (coxeterSystem .F4) δ ∧
      (∀ (i : Fin Tag.F4.rank) (A B : X.Cover (chamberOf 1)),
        (X.universalCover (chamberOf 1)).adj i A B ↔
          δ A B = 1 ∨ δ A B = (coxeterSystem .F4).simple i) ∧
      ∀ (i : Fin Tag.F4.rank) (A : X.Cover (chamberOf 1)),
        (panel (coxeterSystem .F4) δ i A).encard = if (i : ℕ) < 2 then 3 else 5) ∧
    (∀ (i : Fin Tag.F4.rank) (A : X.Cover (chamberOf 1)),
      ((X.universalCover (chamberOf 1)).residue {i} A).encard = if (i : ℕ) < 2 then 3 else 5) ∧
    Finite (X.Cover (chamberOf 1)) ∧ Nat.card (X.Cover (chamberOf 1)) = 371231385525 ∧
    (∀ (g : Eam) (c : Chamber),
      ((chamberRho X hX g : X.typeAut) : Equiv.Perm Chamber) c = chamberMul c g⁻¹) ∧
    (chamberRho X hX).ker = Subgroup.zpowers cE' ∧ Nat.card (Subgroup.zpowers cE') = 2 ∧
    Nonempty (Eam ⧸ Subgroup.zpowers cE' ≃* (chamberRho X hX).range) ∧
    Finite (X.liftSubgroup (chamberOf 1) (chamberRho X hX).range) ∧
    Finite (X.pi2 (chamberOf 1)) ∧ Odd (Nat.card (X.pi2 (chamberOf 1))) ∧
    Nonempty (X.liftSubgroup (chamberOf 1) (chamberRho X hX).range ⧸
        (X.pi2 (chamberOf 1)).subgroupOf (X.liftSubgroup (chamberOf 1) (chamberRho X hX).range) ≃*
      (chamberRho X hX).range) ∧
    Nat.card (X.liftSubgroup (chamberOf 1) (chamberRho X hX).range) =
      153064959367549707878400 ∧
    Nat.card Bam = 824633720832 ∧
    Nat.card Eam * Nat.card (X.pi2 (chamberOf 1)) = 306129918735099415756800 ∧
    ((Pc 0).subgroupOf Eam).index * Nat.card (X.pi2 (chamberOf 1)) = 3968055 := by
  set c₀ : Chamber := chamberOf 1 with hc₀
  set ρ := chamberRho X hX with hρ
  set H := ρ.range with hH
  obtain ⟨δ, hδ, hadj, hpanδ, hpanX⟩ := F4_rank_three_local_building_cover X c₀ hpanel hres2 hres3
  have hsizeΔ : ∀ (i : Fin Tag.F4.rank) (A : X.Cover c₀),
      (panel (coxeterSystem .F4) δ i A).encard = if (i : ℕ) < 2 then 3 else 5 := fun i A => by
    rw [hpanδ, hsize]
  have hq : ∀ i A, (panel (coxeterSystem .F4) δ i A).encard = f4q i + 1 := fun i A => by
    rw [hsizeΔ, f4q]
    split_ifs <;> rfl
  have hfin : Finite (X.Cover c₀) := (card_eq_finsum_weylWeight hδ hq).1
  have hcard : Nat.card (X.Cover c₀) = 371231385525 := by
    rw [(card_eq_finsum_weylWeight hδ hq).2, finsum_weylWeight_f4 hδ hq]
  have hR₁ := finite_ncard_residue_of_isResidueBuilding (q := f4q)
    (hres3 (typesOff 0) (ncard_typesOff 0) c₀) (fun y _ j _ => by
      rw [hsize, f4q]
      split_ifs <;> rfl)
  have hsum : f4WeightSumOff ((0 : Fin 4) : ℕ) = 93555 := f4WeightSumOff_eq.1
  rw [typesOff, finsum_weylWeight_off hδ hq ((0 : Fin 4) : ℕ), hsum] at hR₁
  have hgrp : parJ (typesOff 0) = Pc 0 := parJ_typesOff hP1
  have hB93555 : Nat.card (Pc 0) = Nat.card Bam * 93555 := by
    rw [← hgrp, ← natCard_resGroup, natCard_eq_mul_ncard_image (Bam_le_resGroup _),
      ← residue_chamberOf_one hres, typesOff, hR₁.2]
  have hP1card : Nat.card (Pc 0) = 77148607752437760 := natCard_P1
  have hBcard : Nat.card Bam = 824633720832 := by omega
  have hkerρ : ρ.ker = Subgroup.zpowers cE' := by
    rw [hρ, ker_chamberRho, ker_chamberLeft_eq hker]
  have hc2 := natCard_zpowers_cE' hc
  have hEH : Nat.card Eam = Nat.card H * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hkerρ, hc2]
  have htr : ∀ x y : Chamber, ∃ h ∈ H, (h : Equiv.Perm Chamber) x = y := fun x y => by
    obtain ⟨g, hg⟩ := exists_chamberRho_apply_eq hX x y
    exact ⟨ρ g, ⟨g, rfl⟩, hg⟩
  have hCh : Nat.card Eam = Nat.card Bam * Nat.card Chamber := by
    rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _),
      ← Subgroup.index_eq_card, ← (Bam.subgroupOf Eam).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Bam_le_Eam).toEquiv]
  have hHorb : Nat.card H = Nat.card (MulAction.stabilizer H c₀) * Nat.card Chamber := by
    have : MulAction.IsPretransitive H Chamber := ⟨fun x y => by
      obtain ⟨h, hh, e⟩ := htr x y
      exact ⟨⟨h, hh⟩, e⟩⟩
    rw [← (MulAction.stabilizer H c₀).card_mul_index, MulAction.index_stabilizer,
      MulAction.orbit_eq_univ, Set.ncard_univ]
  have hChpos : 0 < Nat.card Chamber := Nat.card_pos
  have hstab : Nat.card (MulAction.stabilizer H c₀) = 412316860416 := by
    have h1 : Nat.card Bam * Nat.card Chamber =
        (Nat.card (MulAction.stabilizer H c₀) * 2) * Nat.card Chamber := by
      rw [← hCh, hEH, hHorb]
      ring
    have h2 := Nat.eq_of_mul_eq_mul_right hChpos h1
    omega
  have hHt : Nat.card (X.liftSubgroup c₀ H) = 153064959367549707878400 := by
    rw [natCard_liftSubgroup_eq hconn H htr c₀, hstab, hcard]
  have hHK := natCard_liftSubgroup (c₀ := c₀) hconn H
  have hEK : Nat.card Eam * Nat.card (X.pi2 c₀) = 306129918735099415756800 := by
    rw [hEH, mul_comm (Nat.card H) 2, mul_assoc, ← hHK, hHt]
    norm_num
  have hidx : ((Pc 0).subgroupOf Eam).index * Nat.card (X.pi2 c₀) = 3968055 := by
    have h1 := ((Pc 0).subgroupOf Eam).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Pc_le_Eam 0)).toEquiv, hP1card] at h1
    rw [← h1, mul_assoc] at hEK
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) (hEK.trans (by norm_num))
  have hodd : Odd (Nat.card (X.pi2 c₀)) :=
    Odd.of_dvd_nat (by decide) (Dvd.intro_left _ hidx)
  have : Finite (X.LiftPair c₀) := finite_liftPair hconn
  refine ⟨⟨δ, hδ, hadj, hsizeΔ⟩, fun i A => by rw [hpanX, hsize], hfin, hcard,
    chamberRho_apply hX, hkerρ, hc2,
    ⟨(QuotientGroup.quotientMulEquivOfEq hkerρ.symm).trans (QuotientGroup.quotientKerEquivRange ρ)⟩,
    inferInstance, inferInstance, hodd, nonempty_liftSubgroup_quotient_mulEquiv hconn H, hHt,
    hBcard, hEK, hidx⟩

end CFSG.Monster.B.TwoA.Amalgam
